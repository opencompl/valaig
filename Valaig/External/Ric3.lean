import Valaig.External.Basic

namespace Valaig.External

def rIC3 (engine : String := "ic3") (extraArgs : Array String := #[]) : CertifiedSafetyAigerMC :=
  {
    interpretOutput := interpretSatExitCode,
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
