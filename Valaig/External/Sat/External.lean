module

public import Valaig.Aig.Core
public import Lean.CoreM
public import Std.Sat.CNF.Basic
public import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide.Syntax
import all Lean.Meta.Tactic.BVDecide.TacticContext
import Std.Tactic.BVDecide.Reflect

public section
namespace Valaig.Sat.External

structure Config where
  trimProofs : Bool := true
  timeout : Nat := 3600
  binaryProofs : Bool := true

open Lean.Elab.Tactic.BVDecide.Frontend Std.Tactic.BVDecide
open Lean.Meta.Tactic.BVDecide

/--
  Run an external SAT solver on the cnf to obtain an LRAT proof.
  This will obtain an `LratCert` if the formula is UNSAT and an assignment as an array of nats
  and their assignment otherwise.
-/
def solveCnf (cnf : Std.Sat.CNF Nat) (lratPath : System.FilePath) (config : Config := {}) : Lean.CoreM (Except (Array (Bool × Nat)) LratCert) := do
  let solver ← TacticContext.new.determineSolver
  runExternal
    cnf
    solver
    lratPath
    config.trimProofs
    config.timeout
    config.binaryProofs
    .proof

def solveUnsatCnfChecked (cnf : Std.Sat.CNF Nat) (lratPath : System.FilePath) (config : Config := {}) : Lean.CoreM (Except String { _u : Unit // cnf.Unsat }) := do
  match ← solveCnf cnf lratPath config with
  | .error _ => return throw "Sat solver returned SAT"
  | .ok cert =>

  let verified := Reflect.verifyCert cnf cert
  if _ : !verified then
    return throw "Failed to verify UNSAT proof"
  else

  return pure ⟨(), by grind [Reflect.verifyCert_correct]⟩

def solveUnsatChecked (aig : Std.Sat.AIG.Entrypoint Aig.LeafIdx) (config : Config := {}) : Lean.CoreM (Except String { _u : Unit // aig.Unsat }) := do
  let aig := aig.relabelNat
  let cnf := Std.Sat.AIG.toCNF aig
  IO.FS.withTempFile fun _ lratPath => do
    let v ← solveUnsatCnfChecked cnf lratPath config
    return v.map fun x => ⟨(), by grind[Std.Sat.AIG.toCNF_equisat, Std.Sat.AIG.Entrypoint.relabelNat_unsat_iff]⟩

end Valaig.Sat.External
