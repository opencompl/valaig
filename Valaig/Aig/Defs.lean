import Valaig.Aig.Refs

namespace Valaig.Aig

-- We define VarDef and WithSymbol for the two fields that both Inputs/Latches
-- have separately so they are transparently inlined into Inputs/Latches
structure VarDef where
  var : Var
deriving Hashable, DecidableEq, Repr, Inhabited, BEq

namespace VarDef

@[inline, simp]
abbrev idx (self : VarDef) : Nat :=
  self.var.idx

@[inline, simp]
abbrev lit (self : VarDef) : Lit :=
  self.var

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

/--
The metadata of a latch in the Aig
-/
structure Latch extends VarDef, WithSymbol where
  next : Option Lit
  reset : Option Lit := none
deriving Hashable, DecidableEq, Repr, Inhabited

instance : Coe Latch Var where
  coe := (·.var)

/--
An atom in the combinational aig is either an input or a latch, which is just
a reference back to the index in the inputs or latches arrays
-/
inductive Atom where
| input (idx : Nat) : Atom
| latch (idx : Nat) : Atom
deriving Hashable, DecidableEq, Repr, Inhabited

/--
An output of interest in the circuit - this is also used to represent other
nameable nodes in the Aiger format like bad and constraint nodes
-/
structure Output extends WithSymbol where
  lit : Lit
deriving Hashable, DecidableEq, Repr, Inhabited

abbrev Inputs := Array Input
abbrev Latches := Array Latch
abbrev Outputs := Array Output

/--
A raw sequential Aig without any well-formedness invariants. This lets
us define the invariants directly on this, rather than on its fields indirectly
-/
structure Raw where
  -- The underlying AIG
  aig : Std.Sat.AIG Aig.Atom

  -- A mapping from input indices (Atom.input idx) to their definition
  inputs : Inputs

  -- A mapping from latch indices (Atom.latch idx) to their definition
  latches : Latches

section
open Std.Sat AIG
variable {α : Type} (arr : Array α) (idx : α -> Nat)
variable (decls: Array (Decl Atom)) (mkAtom : Nat -> Atom)

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

@[grind]
structure AtomsBij : Prop where
  hinjec : AtomsInj arr idx decls mkAtom
  hsurjec : AtomsSur arr idx decls mkAtom

attribute [simp] AtomsBij.mk

end

namespace Raw

@[simp]
abbrev InputsBij (aig : Raw) :=
  AtomsBij aig.inputs (·.idx) aig.aig.decls Atom.input

@[simp]
abbrev LatchesBij (aig : Raw) :=
  AtomsBij aig.latches (·.idx) aig.aig.decls Atom.latch

@[simp]
abbrev SingleFalse (aig : Raw) :=
  ∀ {i : Nat} (h : i < aig.aig.decls.size), aig.aig.decls[i] = .false ↔ i = 0

@[simp]
abbrev NextStateDefined (aig : Raw) :=
  ∀ {latch} (_ : latch ∈ aig.latches), latch.next.isSome

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

attribute [grind] Aig.Raw.aig
attribute [grind! .] Std.Sat.AIG.hzero
attribute [grind! .] Std.Sat.AIG.hconst
attribute [grind! .] Aig.hfalse
attribute [grind! .] Aig.hinputs
attribute [grind! .] Aig.hlatches

instance : Coe Aig Aig.Raw where
  coe := (·.toRaw)

structure Aig.WF (aig : Aig) where
  -- We specify that each latch must have a next state as an external
  -- well-formedness predicate as
  hnext : aig.toRaw.NextStateDefined

  -- Resets are stratified. TODO: This definition doesn't work as the binary
  -- aiger format requires latches come before gates, so you can't define
  -- interesting reset conditions like this. Instead I think we just want a
  -- generalized form (maybe we should also be able to switch to a mode where
  -- this more restrictive constraint is used, it makes checking for cycles etc
  -- way easier)
  -- hreset : ∀ {latch}, latch ∈ latches → latch.reset.var < latch.var

end Valaig
