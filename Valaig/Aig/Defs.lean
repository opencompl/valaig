import Valaig.Aig.Refs

namespace Valaig.Aig

-- We define VarDef and WithSymbol for the two fields that both Inputs/Latches
-- have separately so they are transparently inlined into Inputs/Latches
structure VarDef where
  var : Var
deriving Hashable, DecidableEq, Repr, Inhabited, BEq

namespace VarDef

@[inline, simp]
abbrev lit (self : VarDef) : Lit :=
  self.var.toLit

end VarDef

structure WithSymbol where
  symbol : String := ""
deriving Hashable, DecidableEq, Repr, Inhabited, BEq

/--
The metadata of an input in the Aig
-/
structure Input extends VarDef, WithSymbol
deriving Hashable, DecidableEq, Repr, Inhabited

instance : Coe Input Var where
  coe := (·.var)

instance : Coe Input Lit where
  coe := (·.lit)

/--
The metadata of a latch in the Aig.

We require all latches to have a next state defined to make it easier to define their semantics,
even though sometimes this next state can't be known at latch construction time as they are cyclic.
To accomodate this, the next value should initially be set to a constant, before being subsequently
overwritten.

We differ from Aiger 1.9 by requiring all latches to have a reset, meaning that all sources of
nondeterminism in the circuit are due to inputs so are easier to reason about.
Resets are stratified (acyclic), by requiring that the reset comes before the variable defined by
this latch. Note that this is not compatible with the binary aiger format, so for binary aiger we
need to reorder things to prevent this. We prefer this encoding as it is easier to reason about as
we have an explicit order on variables.
-/
structure Latch extends VarDef, WithSymbol where
  next : Lit
  reset : Lit
  hreset : reset.var < var
deriving Hashable, DecidableEq, Repr

instance : Coe Latch Var where
  coe := (·.var)

instance : Coe Latch Lit where
  coe := (·.lit)

abbrev InputIdx := Nat
abbrev LatchIdx := Nat

/--
An atom in the combinational aig is either an input or a latch, which is just
a reference back to the index in the inputs or latches arrays
-/
inductive AtomIdx where
| input (idx : InputIdx)
| latch (idx : LatchIdx)
deriving Hashable, DecidableEq, Repr, Inhabited

/--
An output of interest in the circuit - this is also used to represent other
nameable nodes in the Aiger format like bad and constraint nodes
-/
structure Output extends WithSymbol where
  ofRaw ::
    lit : Lit
deriving Hashable, DecidableEq, Repr, Inhabited

def Output.mk (lit : Lit) (symbol : String := "") : Output :=
  { lit, symbol }

abbrev Inputs := Array Input
abbrev Latches := Array Latch
abbrev Outputs := Array Output

/--
A raw sequential Aig without any well-formedness invariants. This lets
us define the invariants directly on this, rather than on its fields indirectly
-/
structure Raw where
  -- The underlying AIG
  aig : Std.Sat.AIG Aig.AtomIdx

  -- A mapping from input indices (AtomIdx.input idx) to their definition
  inputs : Inputs

  -- A mapping from latch indices (AtomIdx.latch idx) to their definition
  latches : Latches

section
open Std.Sat AIG
variable {α : Type} (arr : Array α) (idx : α -> Nat)
variable (decls: Array (Decl AtomIdx)) (mkAtom : Nat -> AtomIdx)

@[simp]
abbrev AtomsInj : Prop :=
  ∀ {iarr : Nat} (harrbound : iarr < arr.size),
  ∃ (hdeclbound : idx arr[iarr] < decls.size),
     decls[idx arr[iarr]] = .atom (mkAtom iarr)

@[simp]
abbrev AtomsSur : Prop :=
  ∀ {idecl : Nat} (hdeclbound : idecl < decls.size),
  ∀ {iarr : Nat} (hdecl : decls[idecl] = .atom (mkAtom iarr)),
  ∃ (harrbound: iarr < arr.size),
    idx arr[iarr] = idecl

@[scoped grind]
structure AtomsBij : Prop where
  hinjec : AtomsInj arr idx decls mkAtom
  hsurjec : AtomsSur arr idx decls mkAtom

attribute [simp] AtomsBij.mk

end
end Aig

@[inline]
def Aig.Raw.size (aig : Aig.Raw) : Nat := aig.aig.decls.size

@[inline]
def Var.validIn (var : Var) (aig : Aig.Raw) : Prop :=
  var.idx < aig.size
deriving Decidable

@[inline, simp]
abbrev Lit.validIn (lit : Lit) (aig : Aig.Raw) := lit.var.validIn aig

abbrev Var.In (aig : Aig.Raw) := { var : Var // var.validIn aig }
abbrev Lit.In (aig : Aig.Raw) := { lit : Lit // lit.validIn aig }

namespace Aig.Raw

@[simp]
abbrev InputsBij (aig : Raw) :=
  AtomsBij aig.inputs (·.var.idx) aig.aig.decls AtomIdx.input

@[simp]
abbrev LatchesBij (aig : Raw) :=
  AtomsBij aig.latches (·.var.idx) aig.aig.decls AtomIdx.latch

@[simp]
abbrev SingleFalse (aig : Raw) :=
  ∀ {i : Nat} (h : i < aig.aig.decls.size), aig.aig.decls[i] = .false ↔ i = 0

@[simp]
abbrev NextsValid (aig : Raw) :=
  ∀ {i : Nat} (h : i < aig.latches.size), aig.latches[i].next.validIn aig

end Aig.Raw

/--
An Aig with added sequential semantics through latches.
We add a number of invariants to preserve that keeps the Aig in a state where
it is easier to reason about/manipulate and that are practical for a future
optimized implementation.
-/
structure Aig extends Aig.Raw where
  -- Only index 0 represents false
  hfalse : toRaw.SingleFalse

  -- There is a bijection between indices in the inputs array and input atoms
  -- in the aig
  hinputs : toRaw.InputsBij

  -- There is a bijection between indices in the latches array and latch atoms
  -- in the aig
  hlatches : toRaw.LatchesBij

  -- The next state variable for each latch is valid in this Aig
  hnexts : toRaw.NextsValid

instance : Coe Aig Aig.Raw where
  coe := (·.toRaw)

end Valaig
