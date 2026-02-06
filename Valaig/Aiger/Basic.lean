module

public import Valaig.Aig.Basic

-- TODO: This shouldn't be necessary but the module system seems broken:
-- https://github.com/leanprover/lean4/issues/12337
import all Valaig.Aig.Basic

public section
namespace Valaig

/--
A thin wrapper over an Aig with additional outputs and invariants for reading/
writing Aiger files.
-/
structure Aiger where
  aig : Aig
  bads : Aig.Outputs

namespace Aiger

structure WellFormed (aig : Aiger) where
  badsValid : ∀ {bad}, bad ∈ aig.bads → bad.lit.validIn aig.aig

@[inline, simp]
abbrev numBads (aig : Aiger) : Nat :=
  aig.bads.size
