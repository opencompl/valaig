import Valaig.Aig.Basic

namespace Valaig

/--
An Aiger model checking problem is a sequential Aig with property nodes tracked
-/
structure Aiger where
  aig : Aig

  -- TODO: The rest of the properties
  bad : Aig.Lit

namespace Aiger

abbrev Atom := Aig.Atom

@[inline]
def size (aiger : Aiger) : Nat := aiger.aig.size

@[inline]
def numConstants (aiger : Aiger) : Nat := aiger.aig.numConstants

@[inline]
def numInputs (aiger : Aiger) : Nat := aiger.aig.numInputs

@[inline]
def numLatches (aiger : Aiger) : Nat := aiger.aig.numLatches

@[inline]
def numAtoms (aiger : Aiger) : Nat := aiger.aig.numAtoms

end Aiger
end Valaig
