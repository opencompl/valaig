module

public import Valaig.External.Basic

public section
namespace Valaig.External

@[reducible]
def rIC3
    (timeoutMs : Option Nat := none)
    (engine : String := "ic3")
    (extraArgs : Array String := #[]) :
    CertifiedSafetyAigerMC :=
  {
    timeoutMs,
    interpretOutput := interpretSatExitCode "rIC3",
    safetyArgs,
    certifiedSafetyArgs,
  }
where
  safetyArgs (problem : System.FilePath) : IO.Process.SpawnArgs :=
    let cmd := "rIC3"
    let args := #["-e", engine] ++ extraArgs |>.push problem.toString
    { cmd, args }

  certifiedSafetyArgs (problem certificate : System.FilePath) : IO.Process.SpawnArgs :=
    let args := safetyArgs problem
    { args with args := args.args.push certificate.toString }

end Valaig.External
