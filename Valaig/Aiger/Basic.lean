import Valaig.Aig.Basic

namespace Valaig

/--
A thin wrapper over an Aig with additional outputs and invariants for reading/
writing Aiger files
-/
structure Aiger where
  aig : Aig
  bads : Aig.Outputs

  hbads : ∀ {bad}, bad ∈ bads → bad.lit.validIn aig := by grind
  -- TODO: Other properties, invariants for them

namespace Aiger

@[inline, simp]
abbrev numBads(aig : Aiger) : Nat := aig.bads.size

end Valaig.Aiger
