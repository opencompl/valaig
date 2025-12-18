import Valaig.Aig.Basic
import Valaig.Aiger.Writer
import Valaig.Result

namespace Valaig.External

open Valaig.Aig

structure ExternalMC where
  interpretOutput (output : IO.Process.Output) : Result

structure SafetyAigerMC extends ExternalMC where
  safetyArgs (problem : System.FilePath) : IO.Process.SpawnArgs

class CertifiedSafetyAigerMC extends SafetyAigerMC where
  certifiedSafetyArgs (problem certificate : System.FilePath) : IO.Process.SpawnArgs

instance : Coe SafetyAigerMC ExternalMC where
  coe := (·.toExternalMC)

instance : Coe CertifiedSafetyAigerMC SafetyAigerMC where
  coe := (·.toSafetyAigerMC)

def interpretSatExitCode (output : IO.Process.Output) : Result :=
  match output.exitCode with
  | 20 => .proof
  | 10 => .counterexample
  | _ => .unknown

def runProcess (args : IO.Process.SpawnArgs) : IO IO.Process.Output := do
  let child ← IO.Process.spawn { args with stdout := .piped, stderr := .piped, stdin := .null }
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated

  let exitCode ← child.wait
  let stdout ← IO.ofExcept stdout.get
  let stderr ← IO.ofExcept stderr.get

  return { exitCode, stdout := stdout, stderr := stderr }

def checkSafety (config : SafetyAigerMC) (aig : Aiger) : IO Result := do
  IO.FS.withTempDir fun dir => do
    let path := dir / "model.aag"
    IO.FS.withFile path .write fun handle => do
      aig.writeAag <| IO.FS.Stream.ofHandle handle
      let out ← runProcess (config.safetyArgs path)
      return config.interpretOutput out

end Valaig.External
