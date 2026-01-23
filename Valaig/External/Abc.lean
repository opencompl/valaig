import Valaig.External.Basic

namespace Valaig.External

-- Currently just an scorr/pdr setup
def Abc (timeoutMs : Option Nat := none) : SafetyAigerMC :=
  {
    timeoutMs,
    supportsAag := false,
    interpretOutput,
    safetyArgs,
  }
where
  safetyArgs (problem : System.FilePath) : IO.Process.SpawnArgs :=
    let cmd := "abc"
    -- Commands from https://github.com/berkeley-abc/abc/issues/281
    -- We use scorr before pdr as it helps on the Blase equivalence checking problems
    let cmdStr := s!"read {problem.toString}; logic; undc; strash; zero; fold; scorr; pdr"
    let args := #["-c", cmdStr]
    { cmd, args }

  interpretOutput (out : IO.Process.Output) : EResult := do
    if out.stdout.contains "Property proved." then
      return Result.proof
    else
      return Result.counterexample

end Valaig.External
