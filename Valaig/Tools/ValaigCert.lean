module

import Valaig.Aiger
import Valaig.Cert
import Valaig.Sat.Std
import Valaig.Sat.External
import Valaig.Transform.Unroll
import Valaig.Transform.TwoLevelSimp
import Std.Sat.AIG.RelabelNat
import Std.Sat.AIG.CNF

open Valaig

set_option warn.sorry false

def liftCoreM (action : Lean.CoreM α) : IO α := do
  let env ← Lean.mkEmptyEnvironment
  let ctx := { fileName := "", fileMap := default }
  let state := { env := env }
  action.toIO' ctx state

def checkUnsat (aig : WFAig) (lit : Lit) (reset : Bool) (valid : lit.validIn aig := by grind) : IO (Except String Unit) := do
  let res := Sat.toStd aig reset
  IO.print s!"({res.fst.decls.size} nodes) "
  let entry : Std.Sat.AIG.Entrypoint Aig.LeafIdx := .mk res.fst (res.snd ⟨lit, valid⟩)
  let relabelled := entry.relabelNat
  let cnf := Std.Sat.AIG.toCNF relabelled
  IO.print s!"({cnf.clauses.size} clauses, {cnf.numLiterals} literals) "
  liftCoreM <| Sat.External.solveUnsatChecked entry

def run (model cert : String) : IO Unit := do
  IO.println "Reading model"
  let model ← IO.FS.Handle.mk model .read
  let (_, model) ← IO.ofExcept <| Valaig.Aiger.parse <| ← model.readBinToEnd
  
  let bad := model.bads[0]!.lit

  IO.println "Reading certificate"
  let cert ← IO.FS.Handle.mk cert .read
  let (_, cert) ← IO.ofExcept <| Valaig.Aiger.parse <| ← cert.readBinToEnd

  let modelaig := Transform.twoLevelSimp (model.aig.toWF sorry)
  let model := { model with aig := modelaig }

  IO.println "Constructing product circuit"
  let (product, invbad) ← IO.ofExcept <| Valaig.Cert.appendCert model cert

  IO.println s!"Product wellformed: {decide product.WF}"

  -- Check that in a reset state the invariant holds
  IO.print "Init: "
  IO.ofExcept <| ← checkUnsat product invbad true sorry
  IO.println "ok"

  -- Check that whenever the invariant holds, the original property does too
  let (product, imp) := product.addAndRaw invbad.invert bad sorry sorry
  IO.print "Implication: "
  IO.ofExcept <| ← checkUnsat product imp false sorry
  IO.println "ok"

  -- Check that the invariant is inductive
  let (product, map) := Transform.unroll product
  let (product, imp) := product.addAndRaw invbad.invert (map.mapLit invbad sorry) sorry sorry
  IO.print "Consecution: "
  IO.ofExcept <| ← checkUnsat product imp false sorry
  IO.println "ok"

  return ()

public def main (args : List String) : IO Unit := do
  match args with
  | [model, cert] => run model cert
  | _ => IO.eprintln "Error: Expected two filename arguments"
