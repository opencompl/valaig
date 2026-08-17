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

def run (model cert : String) : IO Unit := do
  println "Reading model"
  let model ← IO.FS.Handle.mk model .read
  let (_, model) ← IO.ofExcept <| Aiger.parse <| ← model.readBinToEnd

  if _ : ¬model.aig.WF then return
  else

  let #[{ lit := bad, .. }] := model.bads | return

  if _ : ¬bad.validIn model.aig then
    return
  else

  println "Reading certificate"
  let cert ← IO.FS.Handle.mk cert .read
  let (_, cert) ← IO.ofExcept <| Aiger.parse <| ← cert.readBinToEnd

  let #[{ lit := invBad, .. }] := cert.bads | return

  println "Constructing product circuit"
  let (eq:=_) .ok (product, invBad) := Cert.appendCert model cert | return

  if _ : ¬bad.validIn product then
    return
  else

  if _ : ¬ invBad.validIn product then
    return
  else

  let cert := Cert.Checker.new product bad invBad.invert

  println "Init:"
  let .ok init := (← time "init" <| fun _ => liftCoreM <| Sat.External.solveUnsatChecked cert.initAig) |
    return
    -- IO.ofExcept (throw "s CERTIFICATE UNSAFE")

  println "Implication:"
  let .ok imp ← time "imp" <| fun _ => liftCoreM <| Sat.External.solveUnsatChecked cert.impAig |
    return
    -- IO.ofExcept (throw "s CERTIFICATE UNSAFE")

  println "Consectution:"
  let .ok consec ← time "consec" <| fun _ => liftCoreM <| Sat.External.solveUnsatChecked cert.consecAig |
    return
    -- IO.ofExcept (throw "s CERTIFICATE UNSAFE")

  have : model.aig.Unreachable bad := by
    have := @Cert.mono_appendCert
    grind [Cert.Checker.unreachable_of init.property consec.property imp.property]

  println "s CERTIFICATE SAFE"

  return

public def main (args : List String) : IO Unit := do
  match args with
  | [model, cert] => run model cert
  | _ => IO.eprintln "Error: Expected two filename arguments"
