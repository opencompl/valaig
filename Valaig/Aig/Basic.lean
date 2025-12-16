import Std.Sat.AIG.Basic
import Std.Sat.AIG.CachedGates
import Valaig.Aig.Defs
import Valaig.Aig.DefsLemmas
import Valaig.Aig.RefsLemmas

namespace Valaig.Aig.Raw

@[inline]
def size (aig : Raw) : Nat := aig.aig.decls.size

@[inline, simp]
abbrev numInputs (aig : Raw) : Nat := aig.inputs.size

@[inline, simp]
abbrev numLatches (aig : Raw) : Nat := aig.latches.size

-- Number of inputs and latches
@[inline, simp, grind]
def numAtoms (aig : Raw) : Nat := aig.numInputs + aig.numLatches

@[inline]
def maxVar (aig : Raw) : Var := .ofIdx (aig.size - 1)

@[inline, simp]
abbrev numConstants (_ : Raw) : Nat := 1

-- Number of inputs, latches and constants
@[inline, simp, grind]
def numLeaves (aig : Raw) : Nat := aig.numAtoms + aig.numConstants

@[inline, simp, grind]
def numGates (aig : Raw) : Nat := aig.size - aig.numLeaves

end Aig.Raw

@[inline]
def Var.validIn (var : Var) (aig : Aig.Raw) : Prop :=
  var.idx < aig.size
deriving Decidable

@[inline, simp]
abbrev Lit.validIn (lit : Lit) (aig : Aig.Raw) := lit.var.validIn aig

abbrev Var.In (aig : Aig) := { var : Var // var.validIn aig }
abbrev Lit.In (aig : Aig) := { lit : Lit // lit.validIn aig }

namespace Aig

instance Raw.instGetElemVar : GetElem Raw Var (Std.Sat.AIG.Decl AtomIdx) (fun aig var => var.validIn aig) where
  getElem aig var (h := by grind) := aig.aig.decls[var.idx]

@[inline, reducible, simp]
instance instGetElemVar : GetElem Aig Var (Std.Sat.AIG.Decl AtomIdx) (fun aig var => var.validIn aig) where
  getElem aig var (h := by grind) := aig.toRaw[var]'h

instance Raw.instMem : Membership (Std.Sat.AIG.Decl AtomIdx) Raw where
  mem aig decl := decl ∈ aig.aig.decls

@[inline, reducible, simp]
instance instMem : Membership (Std.Sat.AIG.Decl AtomIdx) Aig where
  mem aig decl := decl ∈ aig.toRaw

@[inline]
def VarDef.idx (var : VarDef) (aig : Aig.Raw) (h : var.var.validIn aig := by grind)
    (hatom : aig[var.var] matches .atom _ := by grind) : AtomIdx :=
  match aig[var.var], hatom with
  | .atom idx, _ => idx

@[inline]
def empty : Aig :=
  {
    aig := .empty
    inputs := #[],
    latches := #[],
    hfalse := by simp [Std.Sat.AIG.empty],
    hinputs := by simp [Std.Sat.AIG.empty],
    hlatches := by simp [Std.Sat.AIG.empty],
  }

@[inline]
def nextInputIdx (aig : Aig) : Nat :=
  aig.numInputs

@[inline]
def nextLatchIdx (aig : Aig) : Nat :=
  aig.numLatches

@[inline]
def addInput (aig : Aig) (symbol : String := "") : Aig × Input :=
  -- We don't need to use mkAtomCached as nextInputIdx_notIn_decls guarantees
  -- it would be a miss
  let atom := (.input aig.nextInputIdx)
  let res := aig.aig.mkAtom atom
  let input := { var := .ofRef res.ref, symbol }

  let aig := { aig with
    aig := res.aig,
    inputs := aig.inputs.push input,
    hfalse := by apply hfalse_decls_push ?_ (by apply mkAtom_eq_decls_push) <;> grind only [hfalse],
    hinputs := by
      apply AtomsBij_push_push (by apply mkAtom_eq_decls_push) (by trivial) (hbijec := aig.hinputs)
      · grind only [mkAtom_ref_eq_decls_size, Var.ofRef_idx]
      · grind only [nextInputIdx]
    hlatches := by apply AtomsBij_unchanged_push (by apply mkAtom_eq_decls_push) <;> grind only [hlatches],
  }
  (aig, input)

@[inline]
def addLatch (aig : Aig) (next : Lit) (reset : Option Lit := none) (symbol : String := "") : Aig × Latch :=
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
    hfalse := by apply hfalse_decls_push ?_ (by apply mkAtom_eq_decls_push) <;> grind only [hfalse],
    hinputs := by apply AtomsBij_unchanged_push (by apply mkAtom_eq_decls_push) <;> grind only [hinputs],
    hlatches := by
      apply AtomsBij_push_push (by apply mkAtom_eq_decls_push) (by trivial) (hbijec := aig.hlatches)
      · grind only [mkAtom_ref_eq_decls_size, Var.ofRef_idx]
      · grind only [nextLatchIdx]
  }
  (aig, latch)

@[inline]
def addLatch' (aig : Aig) (reset : Option Lit := none) (symbol : String := "") : Aig × Latch :=
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
    hfalse := by apply hfalse_decls_push ?_ (by apply mkAtom_eq_decls_push) <;> grind only [hfalse],
    hinputs := by apply AtomsBij_unchanged_push (by apply mkAtom_eq_decls_push) <;> grind only [hinputs],
    hlatches := by
      apply AtomsBij_push_push (by apply mkAtom_eq_decls_push) (by trivial) (hbijec := aig.hlatches)
      · grind only [mkAtom_ref_eq_decls_size, Var.ofRef_idx]
      · grind only [nextLatchIdx]
  }
  (aig, latch)

@[inline]
def addGate (aig : Aig) (rhs0 rhs1 : Lit)
    (h0 : rhs0.validIn aig := by grind) (h1 : rhs1.validIn aig := by grind) :
    Aig × Lit :=
  let res := aig.aig.mkAndCached ⟨rhs0.toRef h0, rhs1.toRef h1⟩

  let aig := { aig with
    aig := res.aig,
    hfalse := by
      apply hfalse_decls_append aig.hfalse
      · grind only [Std.Sat.AIG.mkAndCached_decl_eq]
      · grind only [mkAndCached_matches_gate]
      · apply Std.Sat.AIG.mkAndCached_le_size,
    hinputs := by
      apply AtomsBij_unchanged_append aig.hinputs
      · apply Std.Sat.AIG.mkAndCached_le_size
      · grind only [Std.Sat.AIG.mkAndCached_decl_eq]
      · grind only [mkAndCached_matches_gate],
    hlatches := by
      apply AtomsBij_unchanged_append aig.hlatches
      · apply Std.Sat.AIG.mkAndCached_le_size
      · grind only [Std.Sat.AIG.mkAndCached_decl_eq]
      · grind only [mkAndCached_matches_gate],
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
      apply hfalse_decls_append aig.hfalse
      · grind only [Std.Sat.AIG.mkGate_decl_eq]
      · grind only [mkGate_matches_gate]
      · apply Std.Sat.AIG.mkGate_le_size,
    hinputs := by
      apply AtomsBij_unchanged_append aig.hinputs
      · apply Std.Sat.AIG.mkGate_le_size
      · grind only [Std.Sat.AIG.mkGate_decl_eq]
      · grind only [mkGate_matches_gate],
    hlatches := by
      apply AtomsBij_unchanged_append aig.hlatches
      · apply Std.Sat.AIG.mkGate_le_size
      · grind only [Std.Sat.AIG.mkGate_decl_eq]
      · grind only [mkGate_matches_gate]
  }
  (aig, Lit.ofRef res.ref)

@[unbox, grind]
structure finaliseLatches.State (aig : Aig) where
  latches : Latches := aig.latches
  idx : Nat := 0
  hsize : latches.size = aig.latches.size := by grind
  habove : ∀ {i} (_hge : i ≥ idx) (hlt : i < latches.size), latches[i] = aig.latches[i] := by grind
  hvar : ∀ {i} (h : i < latches.size), latches[i].var = aig.latches[i].var := by grind

@[inline]
def finaliseLatches.State.empty (aig : Aig) : State aig :=
  {}

@[inline]
def finaliseLatches (aig : Aig) (nextState : (latch : Latch) -> latch ∈ aig.latches -> Lit.In aig) : Aig :=
  have s := updateLatches
  { aig with
    latches := s.latches,
    hlatches := by
      constructor
      all_goals intro _ h; simp only [s.hvar, s.hsize]
      · apply aig.hlatches.hinjec
      · apply aig.hlatches.hsurjec
  }

where
  updateLatches (s : finaliseLatches.State aig := .empty aig) : finaliseLatches.State aig :=
    if hidx : s.idx ≥ s.latches.size then
      s
    else
      have next := step s (by omega)
      have : next.val.latches.size - next.val.idx < s.latches.size - s.idx := by
        grind only [finaliseLatches.State.hsize]

      updateLatches next
  termination_by s.latches.size - s.idx

  step (s : finaliseLatches.State aig) (h : s.idx < s.latches.size) : { s' : finaliseLatches.State aig // s'.idx = s.idx + 1 } :=
    match s.latches[s.idx].next with
    -- If the next value is already set, do nothing and continue
    | some _ =>
      ⟨{ s with
        idx := s.idx + 1,
        habove := by intro i h; exact s.habove (by omega)
      }, by simp only⟩
    | none =>
      -- Otherwise get the current latch, compute its new next state and then
      -- modify in place
      let latch := s.latches[s.idx]
      have hmem : latch ∈ aig.latches := by
        subst latch; rw [s.habove]; apply Array.getElem_mem; omega
      let next := nextState latch hmem
      let latches := s.latches.modify s.idx fun latch => { latch with next }

      ⟨{ s with
        latches,
        idx := s.idx + 1,

        hsize := by subst latches; rw [Array.size_modify, s.hsize]
        habove := by intros; rw [Array.getElem_modify_of_ne]; apply s.habove; all_goals omega
        hvar := by intros; rw [Array.getElem_modify]; split <;> apply s.hvar
      }, by simp only⟩


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
