import Valaig.Aig.Basic
import Valaig.Aiger.Writer
import Valaig.Result

namespace Valaig.External

open Valaig.Aig

class ExternalMC (Solver : Type) where
  interpretOutput (solver : Solver) (output : IO.Process.Output) : Result

class SafetyAigerMC (Solver : Type) extends ExternalMC Solver where
  safetyArgs (solver : Solver) (problem : System.FilePath) : IO.Process.SpawnArgs

class CertifiedSafetyAigerMC (Solver : Type) extends SafetyAigerMC Solver where
  certifiedSafetyArgs (solver : Solver) (problem certificate : System.FilePath)
    : IO.Process.SpawnArgs

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

def checkSafety {Solver : Type} (solver : Solver) [mc : SafetyAigerMC Solver] (aig : Aiger) : IO Result := do
  IO.FS.withTempDir fun dir => do
    let path := dir / "model.aag"
    IO.FS.withFile path .write fun handle => do
      aig.writeAag <| IO.FS.Stream.ofHandle handle
      let out ← runProcess (mc.safetyArgs solver path)
      return mc.interpretOutput solver out

end Valaig.External
