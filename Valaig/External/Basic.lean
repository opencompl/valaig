module

public import Valaig.Aig.Basic
import all Valaig.Aig.Basic
public import Valaig.Aiger.Writer
public import Valaig.Result

public section
namespace Valaig.External

open Valaig.Aig

structure ExternalMC where
  timeoutMs : Option Nat := none
  interpretOutput (output : IO.Process.Output) : EResult

structure SafetyAigerMC extends ExternalMC where
  safetyArgs (problem : System.FilePath) : IO.Process.SpawnArgs

class CertifiedSafetyAigerMC extends SafetyAigerMC where
  certifiedSafetyArgs (problem certificate : System.FilePath) : IO.Process.SpawnArgs

instance : Coe SafetyAigerMC ExternalMC where
  coe := (·.toExternalMC)

instance : Coe CertifiedSafetyAigerMC SafetyAigerMC where
  coe := (·.toSafetyAigerMC)

def interpretSatExitCode (solver : String) (output : IO.Process.Output) : EResult :=
  match output.exitCode with
  | 20 => return .proof
  | 10 => return .counterexample
  | code => throw <| .external s!"{solver} returned unexpected exit code {code}"

partial def runProcess (timeoutMs : Option Nat) (args : IO.Process.SpawnArgs) : IO (VExcept IO.Process.Output) := do
  let child ← IO.Process.spawn { args with stdout := .piped, stderr := .piped, stdin := .null }
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  match timeoutMs with
  | none =>
    finalise (←child.wait) stdout stderr
  | some timeoutMs =>
    go timeoutMs timeoutMs child stdout stderr

where
  go {cfg} (timeoutMs budgetMs : Nat) (child : IO.Process.Child cfg) (stdout stderr : Task (Except IO.Error String)) :
      IO (VExcept IO.Process.Output) := do
    withTimeoutCheck timeoutMs budgetMs (killAndWait child) do
      match ← child.tryWait with
      | some exitCode =>
        finalise exitCode stdout stderr
      | none =>
        let sleepMs : Nat := min 50 budgetMs
        IO.sleep sleepMs.toUInt32
        go timeoutMs (budgetMs - sleepMs) child stdout stderr

  killAndWait {cfg} (child : IO.Process.Child cfg) : IO Unit := do
    child.kill
    discard child.wait

  withTimeoutCheck {α : Type} (timeoutMs budgetMs : Nat) (cleanup : IO Unit) (x : IO (VExcept α)) :
      IO (VExcept α) := do
    if budgetMs == 0 then
      cleanup
      return .error <| .timeout s!"{args.cmd} {args.args}" timeoutMs
    else
      x

  finalise (exitCode : UInt32) (stdout stderr : Task (Except IO.Error String)) : IO (VExcept IO.Process.Output) := do
    let stdout ← IO.ofExcept stdout.get
    let stderr ← IO.ofExcept stderr.get
    return .ok { exitCode, stdout := stdout, stderr := stderr }

def checkSafety (config : SafetyAigerMC) (aig : Aiger) : IO EResult := do
  IO.FS.withTempDir fun dir => do
    -- Some solvers need the extension to be aag to work correctly so we create
    -- such a file rather than just using withTempFile
    let path := dir / "model.aag"
    IO.FS.withFile path .write fun handle => do
      aig.writeAag <| IO.FS.Stream.ofHandle handle
      let out ← runProcess config.timeoutMs (config.safetyArgs path)
      return out >>= config.interpretOutput

end Valaig.External
