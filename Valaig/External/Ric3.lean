import Valaig.External.Basic

namespace Valaig.External

structure rIC3 where
  engine : String := "ic3"
  extraArgs : Array String := #[]

instance : EmptyCollection rIC3 where
  emptyCollection := {}

instance : ExternalMC rIC3 where
  interpretOutput _ := interpretSatExitCode

instance : SafetyAigerMC rIC3 where
  safetyArgs (ric3 : rIC3) (problem : System.FilePath) : IO.Process.SpawnArgs :=
    let cmd := "rIC3"
    let args := #["-e", ric3.engine] ++ ric3.extraArgs |>.push problem.toString
    { cmd, args }

instance : CertifiedSafetyAigerMC rIC3 where
  certifiedSafetyArgs (ric3 : rIC3) (problem certificate : System.FilePath) : IO.Process.SpawnArgs :=
    let args := SafetyAigerMC.safetyArgs ric3 problem
    { args with args := args.args.push certificate.toString }

end Valaig.External
