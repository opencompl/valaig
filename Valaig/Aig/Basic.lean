import Std.Sat.AIG.Basic
import Std.Sat.AIG.CachedGates
import Valaig.Aig.StdSatLemmas

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

@[inline, simp, grind .]
def ofRef {α} [DecidableEq α] [Hashable α] {aig : Std.Sat.AIG α} (ref : aig.Ref) : Var :=
  .ofIdx ref.gate

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
  (l.idx &&& 1) ≠ 0

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
def constant (value : Bool) : Lit :=
  mk .constant value

@[inline]
def false : Lit :=
  constant .false

@[inline]
def true : Lit :=
  constant .true

@[inline]
def ofFanin (fi : Std.Sat.AIG.Fanin) : Lit :=
  .mk (.ofIdx fi.gate) fi.invert

attribute [coe] ofFanin

@[simp]
theorem mk_var (var : Var) {invert : Bool} :
    (Lit.mk var invert).var = var := by
  simp [mk, Lit.var, Nat.or_div_two]
  have : invert.toNat / 2 = 0 := by
    have := Bool.toNat_le invert
    omega
  simp [this]

@[simp]
theorem mk_inverted {v : Var} (invert : Bool) :
    (Lit.mk v invert).inverted = invert := by
  simp [mk, inverted]
  decide +revert

section
variable {α} [DecidableEq α] [Hashable α] {aig : Std.Sat.AIG α}

@[inline]
def ofRef (ref : aig.Ref) : Lit :=
  .mk (.ofRef ref) ref.invert

@[inline]
def toRef (lit : Lit) (h : lit.var.idx < aig.decls.size) : aig.Ref :=
  .mk lit.var.idx lit.inverted h

@[simp]
theorem ofRef_var_idx_eq_gate (ref : aig.Ref) :
    (ofRef ref |>.var.idx) = ref.gate := by
  simp [ofRef]

end

end Lit

instance : Coe Std.Sat.AIG.Fanin Lit where
  coe := Lit.ofFanin

namespace Var

@[inline]
abbrev toLit (v : Var) : Lit :=
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
abbrev idx (input : Input) : Nat :=
  input.var.idx

@[inline]
abbrev lit (input : Input) : Lit :=
  input.var.toLit

end Input

/--
The metadata of a latch in the Aig
-/
structure Latch where
  var : Var
  next : Option Lit
  reset : Option Lit := none
  symbol : String := ""
deriving Hashable, DecidableEq, Repr, Inhabited

namespace Latch

@[inline]
abbrev idx (latch : Latch) : Nat :=
  latch.var.idx

@[inline]
abbrev lit (latch : Latch) : Lit :=
  latch.var.toLit

end Latch

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
structure Output where
  lit : Lit
  symbol : String := ""
deriving Hashable, DecidableEq, Repr, Inhabited

abbrev Inputs := Array Input
abbrev Latches := Array Latch
abbrev Outputs := Array Output

section
open Std.Sat AIG

@[simp]
abbrev InputsInj (inputs : Inputs) (aig : AIG Atom) : Prop :=
  ∀ (iin : Nat) (hinbound : iin < inputs.size),
  ∃ (hdeclbound : inputs[iin].idx  < aig.decls.size),
    aig.decls[inputs[iin].idx] = .atom (.input iin)

@[simp]
abbrev InputsSur (inputs : Inputs) (aig : AIG Atom) : Prop :=
  ∀ (idecl : Nat) (hdeclbound : idecl < aig.decls.size),
  match aig.decls[idecl] with
  | .atom (.input iin) =>
    ∃ (hinbound: iin < inputs.size), inputs[iin].idx = idecl
  | _ => true

@[grind]
structure InputsBij (inputs : Inputs) (aig : AIG Atom) : Prop where
  hinjec : InputsInj inputs aig
  hsurjec : InputsSur inputs aig

attribute [simp] InputsBij.mk

@[simp]
abbrev LatchesInj (latches : Latches) (aig : AIG Atom) : Prop :=
  ∀ (ilat : Nat) (hlatbound : ilat < latches.size),
  ∃ (hdeclbound : latches[ilat].idx  < aig.decls.size),
    aig.decls[latches[ilat].idx] = .atom (.latch ilat)

@[simp]
abbrev LatchesSur (latches : Latches) (aig : AIG Atom) : Prop :=
  ∀ (idecl : Nat) (hdeclbound : idecl < aig.decls.size),
  match aig.decls[idecl] with
  | .atom (.latch idx) =>
    ∃ (hlatbound: idx < latches.size), latches[idx].idx = idecl
  | _ => true

@[grind]
structure LatchesBij (latches : Latches) (aig : AIG Atom) : Prop where
  hinjec : LatchesInj latches aig
  hsurjec : LatchesSur latches aig

attribute [simp] LatchesBij.mk

end

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
  inputs : Aig.Inputs

  -- A mapping from latch indices (Atom.latch idx) to their definition
  latches : Aig.Latches

  -- A set of literals that should never be true
  bads : Aig.Outputs

  -- Only index 0 represents false
  hfalse : ∀ (i : Nat) (h : i < aig.decls.size), aig.decls[i] = .false ↔ i = 0

  -- There is a bijection between indices in the inputs array and input atoms
  -- in the aig
  hinputmap : Aig.InputsBij inputs aig

  -- There is a bijection between indices in the latches array and latch atoms
  -- in the aig
  hlatchmap : Aig.LatchesBij latches aig

  -- Resets are stratified. TODO: This definition doesn't work as the binary
  -- aiger format requires latches come before gates, so you can't define
  -- interesting reset conditions like this. Instead I think we just want a
  -- generalized form (maybe we should also be able to switch to a mode where
  -- this more restrictive constraint is used, it makes checking for cycles etc
  -- way easier)
  -- hreset : ∀ {latch}, latch ∈ latches → latch.reset.var < latch.var

structure Aig.WF (aig : Aig) where
  -- We specify that each latch must have a next state as an external
  -- well-formedness predicate as
  hnext : ∀ {latch}, latch ∈ aig.latches → latch.next.isSome

  -- TODO: Should other predicates be here too? There are other cases when it
  -- could be nice to be able to momentarily break invariants, in particular
  -- hreset

-- Allow grind to get at the Aig invariants
attribute [grind =] Aig.aig
attribute [grind! .] Std.Sat.AIG.hzero
attribute [grind! .] Std.Sat.AIG.hconst
attribute [grind =] Aig.hfalse
attribute [grind! .] Aig.hinputmap
attribute [grind! .] Aig.hlatchmap

namespace Aig

@[inline, simp]
abbrev size (aig : Aig) : Nat := aig.aig.decls.size

@[inline]
abbrev numConstants (_ : Aig) : Nat := 1

@[inline]
abbrev numInputs (aig : Aig) : Nat := aig.inputs.size

@[inline]
abbrev numLatches (aig : Aig) : Nat := aig.latches.size

-- Number of inputs and latches
@[inline]
def numAtoms (aig : Aig) : Nat := aig.numInputs + aig.numLatches

-- Number of inputs, latches and constants
@[inline]
def numLeaves (aig : Aig) : Nat := aig.numAtoms + aig.numConstants

@[inline]
def numGates (aig : Aig) : Nat := aig.size - aig.numLeaves

@[inline]
abbrev numBads (aig : Aig) : Nat := aig.bads.size

@[inline]
def maxVar (aig : Aig) : Var := .ofIdx (aig.size - 1)

@[inline]
def Lit.validIn (lit : Lit) (aig : Aig) := lit.var.idx < aig.size

@[inline]
def empty : Aig :=
  {
    aig := .empty
    inputs := #[],
    latches := #[],
    bads := #[],
    hfalse := by simp [Std.Sat.AIG.empty],
    hinputmap := by simp [Std.Sat.AIG.empty],
    hlatchmap := by simp [Std.Sat.AIG.empty],
  }

@[inline]
abbrev nextInputIdx (aig : Aig) : Nat :=
  aig.numInputs

@[inline]
abbrev nextLatchIdx (aig : Aig) : Nat :=
  aig.numLatches

theorem nextInputIdx_notIn_decls (aig : Aig) {i : Nat} (h : i < aig.size) :
    aig.aig.decls[i] ≠ .atom (.input aig.nextInputIdx) := by
  grind

theorem nextLatchIdx_notIn_decls (aig : Aig) {i : Nat} (h : i < aig.size) :
    aig.aig.decls[i] ≠ .atom (.latch aig.nextLatchIdx) := by
  grind

@[inline]
def addInput (aig : Aig) (symbol : String := "") : Aig × Lit :=
  -- We don't need to use mkAtomCached as nextInputIdx_notIn_decls guarantees
  -- it would be a miss
  let res := aig.aig.mkAtom <| .input aig.nextInputIdx
  let input := { var := .ofRef res.ref, symbol }

  let aig := { aig with
    aig := res.aig,
    inputs := aig.inputs.push input,
    hfalse := by grind,
    hinputmap := by grind,
    hlatchmap := by grind,
  }
  (aig, input.lit)

@[inline]
def addLatch (aig : Aig) (next : Lit) (reset : Option Lit := none) (symbol : String := "") : Aig × Lit :=
  -- We don't need to use mkAtomCached as nextLatchIdx_notIn_decls guarantees
  -- it would be a miss
  let res := aig.aig.mkAtom <| .latch aig.nextLatchIdx
  let latch := {
    var := .ofRef res.ref,
    next,
    reset,
    symbol
  }

  let aig := { aig with
    aig := res.aig,
    latches := aig.latches.push latch,
    hfalse := by grind,
    hinputmap := by grind,
    hlatchmap := by grind,
  }
  (aig, latch.lit)

@[inline]
def addLatch' (aig : Aig) (reset : Option Lit := none) (symbol : String := "") : Aig × Lit :=
  -- We don't need to use mkAtomCached as nextLatchIdx_notIn_decls guarantees
  -- it would be a miss
  let res := aig.aig.mkAtom <| .latch aig.nextLatchIdx
  let latch := {
    var := .ofRef res.ref,
    next := none,
    reset,
    symbol
  }

  let aig := { aig with
    aig := res.aig,
    latches := aig.latches.push latch,
    hfalse := by grind,
    hinputmap := by grind,
    hlatchmap := by grind,
  }
  (aig, latch.lit)

@[inline]
def addGate (aig : Aig) (rhs0 rhs1 : Lit)
    (h0 : rhs0.validIn aig := by grind) (h1 : rhs1.validIn aig := by grind) :
    Aig × Lit :=
  let res := aig.aig.mkAndCached ⟨rhs0.toRef h0, rhs1.toRef h1⟩

  let aig := { aig with
    aig := res.aig,
    hfalse := by
      intro i
      by_cases i < aig.size
      · grind
      · -- For some reason if I remove this grind hits an error
        have : i ≠ 0 := by grind only [Std.Sat.AIG.hzero]
        grind,
    hinputmap := by grind
    hlatchmap := by grind
  }
  (aig, Lit.ofRef res.ref)

@[inline]
def addGateUncached (aig : Aig) (rhs0 rhs1 : Lit)
    (h0 : rhs0.validIn aig := by grind) (h1 : rhs1.validIn aig := by grind) :
    Aig × Lit :=
  let res := aig.aig.mkGate ⟨rhs0.toRef h0, rhs1.toRef h1⟩

  let aig := { aig with
    aig := res.aig,
    hfalse := by
      intro i
      by_cases i < aig.size
      · grind
      · -- For some reason if I remove this grind hits an error
        have : i ≠ 0 := by grind only [Std.Sat.AIG.hzero]
        grind,
    hinputmap := by grind
    hlatchmap := by grind
  }
  (aig, Lit.ofRef res.ref)

@[inline]
def addBad (aig : Aig) (lit : Lit) (symbol : String := "") (_h : lit.validIn aig := by grind) : Aig :=
  { aig with bads := aig.bads.push { lit, symbol } }

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
