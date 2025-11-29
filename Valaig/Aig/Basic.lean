import Std.Sat.AIG

namespace Valaig
namespace Aig

structure Var where
  ofIdx :: 
    idx : Nat
deriving Hashable, DecidableEq, Repr, Inhabited, Ord, BEq

instance : LE Var := leOfOrd
instance : LT Var := ltOfOrd

namespace Var

@[inline]
def constant : Var :=
  .ofIdx 0

@[inline]
def offset (v : Var) (n : Nat) : Var :=
  .ofIdx <| (v.idx + n)

@[inline]
def next (v : Var) : Var :=
  v.offset 1

end Var

structure Lit where
  ofIdx ::
    idx : Nat
deriving Hashable, DecidableEq, Repr, Inhabited, BEq

namespace Lit

@[inline]
def mk (v : Var) (invert : Bool := false) : Lit :=
  .ofIdx <| v.idx * 2 ||| invert.toNat

@[inline]
def var (l : Lit) : Var :=
  .ofIdx <| l.idx / 2

@[inline]
def invert (l : Lit) : Lit :=
  .ofIdx <| l.idx ^^^ 1

@[inline]
def inverted (l : Lit) : Bool :=
  (l.idx &&& 1) != 0

@[inline]
def defines (l : Lit) : Option Var :=
  if !l.inverted then some l.var else none

@[inline]
def isConstant (l : Lit) : Bool :=
  l.var = .constant

@[inline]
def isFalse (l : Lit) : Bool :=
  l.isConstant ∧ !l.inverted

@[inline]
def isTrue (l : Lit) : Bool :=
  l.isConstant ∧ l.inverted

@[inline]
def ofFanin (fi : Std.Sat.AIG.Fanin) : Lit :=
  .mk (.ofIdx fi.gate) fi.invert

attribute [coe] ofFanin

@[inline]
def ofRef {α} [DecidableEq α] [Hashable α] {aig : Std.Sat.AIG α} (ref : aig.Ref) : Lit :=
  .mk (.ofIdx ref.gate) ref.invert

end Lit

instance : Coe Std.Sat.AIG.Fanin Lit where
  coe := Lit.ofFanin

namespace Var

@[inline]
def toLit (v : Var) : Lit :=
  Lit.mk v

end Var

/--
The metadata of an input in the Aig
-/
structure Input where
  var : Var
  symbol : String := ""
deriving Hashable, DecidableEq, Repr, Inhabited

namespace Input

@[inline]
def idx (input : Input) :=
  input.var.idx

end Input

/--
The metadata of a latch in the Aig
-/
structure Latch where
  var : Var
  next : Lit
  reset : Lit
  symbol : String := ""
deriving Hashable, DecidableEq, Repr, Inhabited

namespace Latch

@[inline]
def idx (latch : Latch) :=
  latch.var.idx

end Latch

/--
An atom in the combinational aig is either an input or a latch, which is just
a reference back to the index in the inputs or latches arrays
-/
inductive Atom where
| input : Nat -> Atom
| latch : Nat -> Atom
deriving Hashable, DecidableEq, Repr, Inhabited

/--
An output of interest in the circuit - this is also used to represent other
nameable nodes in the Aiger format like bad and constraint nodes
-/
structure Output where
  lit : Lit
  symbol : String := ""
deriving Hashable, DecidableEq, Repr, Inhabited

end Aig

/--
An Aig with added sequential semantics through latches and Aiger style outputs,
We add a number of invariants to preserve that keeps the Aig in a state where
it is easier to reason about/manipulate and that are practical for a future
optimized implementation.
-/
structure Aig where
  -- The underlying AIG
  aig : Std.Sat.AIG Aig.Atom

  -- A mapping from input indices (Atom.input idx) to their definition
  inputs : Array Aig.Input

  -- A mapping from latch indices (Atom.latch idx) to their definition
  latches : Array Aig.Latch

  -- A set of literals that should never be true
  bads : Array Aig.Output

  -- Only index 0 represents false
  hfalse : ∀ {i} (h : i < aig.decls.size), aig.decls[i] = .false ↔ i = 0

  -- Input indices map to corresponding atoms
  hinputstodecl :
    ∀ {iin idecl} (hin : iin < inputs.size)
      (_ : inputs[iin].idx = idecl),
    ∃ (hdecl : idecl < aig.decls.size),
      aig.decls[idecl] = .atom (.input iin)

  -- Input atoms map to corresponding indices
  hdecltoinputs :
    ∀ {iin idecl} (hdecl : idecl < aig.decls.size)
      (_ : aig.decls[idecl] = .atom (.input iin)),
    ∃ (hin : iin < inputs.size),
      inputs[iin].idx = idecl

  -- Latch indices map to corresponding atoms
  hlatchestodecl :
    ∀ {ilat idecl} (hlat : ilat < latches.size)
      (_ : latches[ilat].idx = idecl),
    ∃ (hdecl : idecl < aig.decls.size),
      aig.decls[idecl] = .atom (.latch ilat)

  -- Latch atoms map to corresponding indices
  hdecltolatches :
    ∀ {ilat idecl} (hdecl : idecl < aig.decls.size)
      (_ : aig.decls[idecl] = .atom (.latch ilat)),
    ∃ (hlat : ilat < latches.size),
      latches[ilat].idx = idecl

  -- Resets are stratified. TODO: This definition doesn't work as the binary
  -- aiger format requires latches come before gates, so you can't define
  -- interesting reset conditions like this. Instead I think we just want a
  -- generalized form (maybe we should also be able to switch to a mode where
  -- this more restrictive constraint is used, it makes checking for cycles etc
  -- way easier)
  -- hreset : ∀ {latch}, latch ∈ latches → latch.reset.var < latch.var

namespace Aig

@[inline]
def size (aig : Aig) : Nat := aig.aig.decls.size

@[inline]
def numConstants (_ : Aig) : Nat := 1

@[inline]
def numInputs (aig : Aig) : Nat := aig.inputs.size

@[inline]
def numLatches (aig : Aig) : Nat := aig.latches.size

-- Number of inputs and latches
@[inline]
def numAtoms (aig : Aig) : Nat := aig.numInputs + aig.numLatches

-- Number of inputs, latches and constants
@[inline]
def numLeaves (aig : Aig) : Nat := aig.numAtoms + aig.numConstants

@[inline]
def numGates (aig : Aig) : Nat := aig.size - aig.numLeaves

@[inline]
def numBads (aig : Aig) : Nat := aig.bads.size

@[inline]
def maxVar (aig : Aig) : Var := .ofIdx (aig.size - 1)

-- [>-
-- A timeframe in the execution of the model, starting from the initial state at 0
-- -/
-- abbrev Frame := Nat

-- structure Entrypoint (α : Type) [DecidableEq α] [Hashable α] where
--   [>-
--   The Aig that we are in.
--   -/
--   aig : Aig α
--   [>-
--   The reference to the node in `aig` that this `Entrypoint` targets.
--   -/
--   ref : aig.Ref
--   [>-
--   The timeframe that this `Entrypoint` targets.
--   -/
--   frame : Frame

-- @[inline]
-- def Entrypoint.toAIGEntrypoint (entry : Entrypoint α) : AIG.Entrypoint (Atom α) :=
--   { aig := entry.aig.aig, ref := entry.ref }

-- def denote (assign : α -> Frame -> Bool) (entry : Entrypoint α) : Bool :=
--   sorry
-- -- TODO: Reasoning about termination of this is somewhat annoying because of how
-- -- it sends a callback into AIG.denote, is there a better way of formalising this?
-- --     AIG.denote assignAtFrame entry.toAIGEntrypoint
--   -- where
-- --     assignAtFrame (atom : Atom α) : Bool :=
-- --       match atom with
-- --       | .input a => assign a entry.frame
-- --       | .latch idx =>
-- --         let latch := entry.aiger.latches[idx]'(sorry)
-- --         match entry.frame with
-- --         | 0 => denote assign { entry with ref := latch.reset, frame := 0 }
-- --         | Nat.succ n =>  denote assign { entry with ref := latch.next, frame := n - 1 }

end Aig

end Valaig
