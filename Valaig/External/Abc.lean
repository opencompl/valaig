import Valaig.External.Basic

namespace Valaig.External

def Abc.dsec (timeoutMs : Option Nat := none) : SafetyAigerMC :=
  {
    timeoutMs,
    supportsAag := false,
    interpretOutput,
    safetyArgs,
  }
where
  safetyArgs (problem : System.FilePath) : IO.Process.SpawnArgs :=
    let cmd := "abc"
    let cmdStr := s!"read {problem.toString}; "
    let args := #["-c", cmdStr]
    { cmd, args }

  interpretOutput (out : IO.Process.Output) : EResult := do
    if out.stdout.contains "Networks are equivalent." then
      return Result.proof
    else
      return Result.counterexample

end Valaig.External
