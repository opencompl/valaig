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

  if _ : ¬model.aig.WF then
    IO.ofExcept (.error "model not wellformed")
  else

  let #[{ lit := bad, .. }] := model.bads | IO.ofExcept (.error "expected single bad in model")

  if _ : ¬bad.validIn model.aig then
    IO.ofExcept (.error "bad not valid in model")
  else

  println "Reading certificate"
  let cert ← IO.FS.Handle.mk cert .read
  let (_, cert) ← IO.ofExcept <| Aiger.parse <| ← cert.readBinToEnd

  let #[{ lit := invBad, .. }] := cert.bads | IO.ofExcept (.error "expected single bad in certificate")

  println "Constructing product circuit"
  let (eq:=_) .ok (product, invBad) := Cert.appendCert model cert | IO.ofExcept (.error "failed to construct product circuit")

  have : bad.validIn product := by have := @Cert.mono_appendCert; grind
  have : invBad.validIn product := by have := @Cert.validIn_appendCert_snd; grind

  let cert := Cert.Checker.new product bad invBad.invert

  println "Init:"
  let .ok init := (← time "init" <| fun _ => liftCoreM <| Sat.External.solveUnsatChecked cert.initAig) |
    IO.ofExcept (.error "s CERTIFICATE UNSAFE")

  println "Implication:"
  let .ok imp ← time "imp" <| fun _ => liftCoreM <| Sat.External.solveUnsatChecked cert.impAig |
    IO.ofExcept (.error "s CERTIFICATE UNSAFE")

  println "Consecution:"
  let .ok consec ← time "consec" <| fun _ => liftCoreM <| Sat.External.solveUnsatChecked cert.consecAig |
    IO.ofExcept (.error "s CERTIFICATE UNSAFE")

  have : model.aig.Unreachable bad := by
    have := @Cert.mono_appendCert
    grind [Cert.Checker.unreachable_of init.property consec.property imp.property]

  println "s CERTIFICATE SAFE"

  return

public def main (args : List String) : IO Unit := do
  match args with
  | [model, cert] => run model cert
  | _ => IO.eprintln "Error: Expected two filename arguments"
