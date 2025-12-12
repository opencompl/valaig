import Valaig.Aig.Basic

namespace Valaig

/--
An extension of the sequential Aig to Aiger outputs
-/
structure Aiger extends Aig where
  bads : Aig.Outputs

  -- TODO: Other properties, invariants for them

instance : Coe Aiger Aig where
  coe := (·.toAig)

namespace Aiger

@[inline]
def ofAig (aig : Aig) : Aiger :=
  {
    toAig := aig,
    bads := #[]
  }

@[inline]
def empty : Aiger :=
  ofAig .empty

@[inline, simp]
abbrev numBads(aig : Aiger) : Nat := aig.bads.size

@[inline]
def addBad (aig : Aiger) (lit : Lit) (symbol : String := "") (_h : lit.validIn aig := by grind) : Aiger :=
  { aig with bads := aig.bads.push { lit, symbol } }

end Valaig.Aiger
