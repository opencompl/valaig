module

import Valaig.External.Aiger
import Valaig.External.Cert
import Valaig.External.Sat.Std
import Valaig.External.Sat.External
import Valaig.Transform.Unroll
import Valaig.Transform.TwoLevelSimp
import Std.Sat.AIG.RelabelNat
import Std.Sat.AIG.CNF

open Valaig

set_option warn.sorry false

def println (s : String) : IO Unit := do
  IO.println s
  (←IO.getStdout).flush

def time {α : Type} (s : String) (m : Unit -> IO α) : IO α := do
  let start ← IO.monoNanosNow
  let res ← m ()
  let finish ← IO.monoNanosNow
  let ms := (finish - start).toFloat / 1_000_000_000
  IO.println s!"t {s}: {ms}"
  return res

def liftCoreM (action : Lean.CoreM α) : IO α := do
  let env ← Lean.mkEmptyEnvironment
  let ctx := { fileName := "", fileMap := default }
  let state := { env := env }
  action.toIO' ctx state

def checkUnsat (aig : WFAig) (lit : Lit) (reset : Bool) (valid : lit.validIn aig := by grind) : IO (Except String Unit) := do
  let res := Sat.toStd aig reset lit.var
  println s!"{res.fst.decls.size} nodes "
  let entry : Std.Sat.AIG.Entrypoint Aig.LeafIdx := .mk res.fst (res.snd ⟨lit, valid⟩)
  -- let relabelled := entry.relabelNat
  -- let cnf := Std.Sat.AIG.toCNF relabelled
  -- print s!"({cnf.clauses.size} clauses, {cnf.numLiterals} literals) "
  liftCoreM <| Sat.External.solveUnsatChecked entry

def run (model cert : String) : IO Unit := do
  println "Reading model"
  let model ← IO.FS.Handle.mk model .read
  let (_, model) ← IO.ofExcept <| Valaig.Aiger.parse <| ← model.readBinToEnd

  let bad := model.bads[0]!.lit

  println "Reading certificate"
  let cert ← IO.FS.Handle.mk cert .read
  let (_, cert) ← IO.ofExcept <| Valaig.Aiger.parse <| ← cert.readBinToEnd

  -- let modelaig := Transform.twoLevelSimp (model.aig.toWF sorry)
  -- let model := { model with aig := modelaig }

  println "Constructing product circuit"
  let (product, invbad) ← time "product" <| fun _ => IO.ofExcept <| Valaig.Cert.appendCert model cert

  if !product.WF then
    IO.ofExcept <| .error "Product not wellformed!"

  -- Check that in a reset state the invariant holds
  println "Init: "
  IO.ofExcept <| ← time "init" <| fun _ => checkUnsat product invbad true sorry
  println "ok"

  -- Check that whenever the invariant holds, the original property does too
  let (product, imp) := product.addAnd invbad.invert bad sorry sorry
  println "Implication: "
  IO.ofExcept <| ← time "implication" <| fun _ => checkUnsat product imp false sorry
  println "ok"

  -- Check that the invariant is inductive
  let (product, map) := Transform.unroll product
  let (product, imp) := product.addAnd invbad.invert (map.mapLit invbad sorry) sorry sorry
  println "Consecution: "
  IO.ofExcept <| ← time "consecution" <| fun _ => checkUnsat product imp false sorry
  println "ok"

  println "s CERTIFICATE SAFE"

  return ()

public def main (args : List String) : IO Unit := do
  match args with
  | [model, cert] => run model cert
  | _ => IO.eprintln "Error: Expected two filename arguments"
