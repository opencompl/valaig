module

import all Valaig.Aig.Basic
public import Valaig.Aig.ValidIn

public section
namespace Valaig.Aig

/-
Iterator types for iterating over valid indices/variables in the Aig.
-/

/--
A generic iterator that forward iterates over a range of valid indices. This
is specialised to produce input/latch indices and variables.
-/
structure GenericIter {α : Type} (mk : Nat -> α) (size : Nat) (valid : α -> Prop) where
  idx : Nat

namespace GenericIter

/--
The parameters to GenericIter are lawful if valid corresponds to the index
being below the size. This is separated outside GenericIter to make it easier
to infer.
-/
class LawfulValid {α : Type} (mk : Nat -> α) (size : Nat) (valid : α -> Prop) : Prop where
  valid : ∀ {out : α}, valid out ↔ ∃ (n : Nat) (_ : out = mk n), n < size

variable {α : Type} {mk : Nat -> α} {size : Nat} {valid : α -> Prop}
variable {m : Type -> Type _} [Pure m] {n : Type _ -> Type _}

@[inline]
instance instIterator : Std.Iterator (GenericIter mk size valid) m α where
  IsPlausibleStep it step :=
    let idx := it.internalState.idx
    match step with
    | .yield it' out => idx < size ∧ it'.internalState.idx = idx + 1 ∧ out = mk idx
    | .skip _ => False
    | .done => idx ≥ size

  step it := pure <| .deflate <|
    let s := it.internalState
    if h : s.idx < size then
      .yield ⟨⟨s.idx + 1⟩⟩ (mk s.idx) (by grind)
    else
      .done (by grind)

attribute [local grind =] Std.IterM.Step.toPure_yield Std.IterM.Step.toPure_skip Std.IterM.Step.toPure_done
attribute [local grind] Std.PlausibleIterStep.yield Std.PlausibleIterStep.skip Std.PlausibleIterStep.done
attribute [local grind =] Std.IterStep.successor_yield Std.IterStep.successor_skip Std.IterStep.successor_done
attribute [local grind =] Std.IterStep.mapIterator_yield
attribute [local simp, local grind] Std.Iterator.step Std.Iter.step Std.IterM.step
attribute [local simp, local grind unfold] Std.Iter.toIterM Std.IterM.toIter
attribute [local grind =] Std.Shrink.inflate_deflate
attribute [local grind .] Std.Iter.IsPlausibleIndirectOutput.direct
attribute [local grind .] Std.Iter.IsPlausibleIndirectOutput.indirect
attribute [local simp, local grind unfold] Std.IterM.IsPlausibleStep
attribute [local simp, local grind unfold] Std.Iter.IsPlausibleStep
attribute [local simp, local grind unfold] Std.Iterator.IsPlausibleStep
attribute [local simp] Std.Iter.IsPlausibleOutput
attribute [local simp] Std.Iter.IsPlausibleSuccessorOf
attribute [local simp, local grind unfold] Std.IterM.IsPlausibleOutput
attribute [local simp, local grind unfold] Std.IterM.IsPlausibleSuccessorOf

open Std.Iterators in
private def instFinitenessRelation : FinitenessRelation (GenericIter mk size valid) m where
  Rel := InvImage WellFoundedRelation.rel (size - ·.internalState.idx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by simp_wf; grind

instance instFinite : Std.Iterators.Finite (GenericIter mk size valid) m := by
  exact .of_finitenessRelation instFinitenessRelation

@[always_inline]
instance instIteratorLoop [Monad m] [Monad n] :
    Std.IteratorLoop (GenericIter mk size valid) m n :=
  .defaultImplementation

variable {it it' : @Std.Iter (GenericIter mk size valid) α} {out : α}

@[simp, grind .]
theorem step_ne_skip {it'} :
    it.step.val ≠ .skip it' := by
  simp; grind

@[local simp]
private theorem successor_isSome_iff_idx_lt_size :
    it.step.val.successor.isSome ↔ it.internalState.idx < size := by
  simp; grind

local grind_pattern successor_isSome_iff_idx_lt_size => it.step.val.successor

@[local simp, local grind =]
private theorem successor_idx_eq_idx_add_one (lt : it.internalState.idx < size) :
    (it.step.val.successor.get (by grind) |>.internalState.idx) = it.internalState.idx + 1 := by
  simp; grind

@[local simp]
private theorem successor_eq_idx_add_one (lt : it.internalState.idx < size) :
    it.step.val.successor.get (by grind) = ⟨⟨it.internalState.idx + 1⟩⟩ := by
  simp; grind

local grind_pattern successor_eq_idx_add_one => it.step.val.successor

@[local simp, local grind =]
private theorem IsPlausibleOutput_iff :
    it.IsPlausibleOutput out ↔
      it.internalState.idx < size ∧ out = mk it.internalState.idx := by
  simp
  intros
  exists ⟨⟨it.internalState.idx + 1⟩⟩

@[local simp, local grind =]
private theorem IsPlausibleSuccessorOf_iff {it' : @Std.Iter (GenericIter mk size valid) α} :
    it'.IsPlausibleSuccessorOf it ↔
      it.internalState.idx < size ∧
      it'.internalState.idx = it.internalState.idx + 1 := by
  constructor
  · grind [Std.Iter.IsPlausibleSuccessorOf]
  · rw [Std.Iter.isPlausibleSuccessorOf_iff_exists]
    intros
    exists it.step.val
    grind [Std.Iter, GenericIter]

@[local simp, local grind =]
private theorem IsPlausibleIndirectOutput_iff :
    it.IsPlausibleIndirectOutput out ↔
      ∃ (n : Nat) (_ : n < size) (_ : n ≥ it.internalState.idx), mk n = out := by
  constructor
  · intro h
    induction h <;> grind
  · rintro ⟨n, h1, h2, h3⟩
    induction h : (size - it.internalState.idx) generalizing it
    case zero => grind
    case succ n' ih =>
      let it' := it.step.val.successor.get <| by grind
      grind [Std.Iter.IsPlausibleIndirectOutput.indirect (it' := it')]

@[simp, grind =]
theorem IsPlausibleIndirectOutput_toIterM_iff :
    it.toIterM.IsPlausibleIndirectOutput out ↔
      ∃ (n : Nat) (_ : n < size) (_ : n ≥ it.internalState.idx), mk n = out := by
  rw [←Std.Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM]
  simp

@[always_inline, inline]
instance instForIn' [Monad n] [lawful : LawfulValid mk size valid] :
    ForIn' n (@Std.Iter (GenericIter mk size valid) α) α ⟨fun _ out => valid out⟩ where
  forIn' it init f :=
    Std.IteratorLoop.finiteForIn' (fun _ _ f c => f c.run) |>.forIn' it.toIterM init
      fun out h acc => f out (by grind [lawful.valid]) acc

@[local simp, local grind =]
private theorem length_eq_size_sub_idx :
    it.length = size - it.internalState.idx := by
  induction hi : size - it.internalState.idx generalizing it
  <;> rw [Std.Iter.length_eq_match_step]
  <;> simp
  <;> grind

@[simp]
theorem length_lt_yield {it' out} (eq : it.step.val = .yield it' out) :
    it'.length < it.length := by
  grind

grind_pattern length_lt_yield => it'.length < it.length, Std.IterStep.yield it' out, it.step
grind_pattern length_lt_yield => it'.length ≤ it.length, Std.IterStep.yield it' out, it.step
grind_pattern length_lt_yield => it'.length > it.length, Std.IterStep.yield it' out, it.step
grind_pattern length_lt_yield => it'.length ≥ it.length, Std.IterStep.yield it' out, it.step

@[simp]
theorem length_lt_skip {it'} (eq : it.step.val = .skip it') :
    it'.length < it.length := by
  grind

grind_pattern length_lt_skip => it'.length < it.length, Std.IterStep.skip it', it.step
grind_pattern length_lt_skip => it'.length ≤ it.length, Std.IterStep.skip it', it.step
grind_pattern length_lt_skip => it'.length > it.length, Std.IterStep.skip it', it.step
grind_pattern length_lt_skip => it'.length ≥ it.length, Std.IterStep.skip it', it.step

/-
This isn't public as the ordering of elements is an implementation detail, we may wish to
move to hashmaps or similar for inputs/latches.
-/
@[simp, grind =]
private theorem toList_eq_ofFn_mk_idx_add :
    it.toList = List.ofFn (fun (n : Fin it.length) => mk (it.internalState.idx + n)) := by
  rw [length_eq_size_sub_idx]
  induction hi : size - it.internalState.idx generalizing it
  · grind [Std.Iter.toList_eq_match_step]
  · rw [Std.Iter.toList_eq_match_step]
    split
    · simp; grind
    · grind
    · simp_all; grind

variable {idx : α}

@[simp, grind =]
private theorem mem_toList_iff_valid_of_idx_eq_zero [lawful : LawfulValid mk size valid]
    (h : it.internalState.idx = 0) :
    idx ∈ it.toList ↔ valid idx := by
  constructor
  · grind [@Fin.is_lt, @lawful.valid]
  · simp
    intro h
    rw [lawful.valid] at h
    rcases h with ⟨n, _⟩
    exists ⟨n, by grind⟩
    grind

private theorem yield_idx_eq_internalState (h : it.step.val = .yield it' idx) :
    idx = mk it.internalState.idx := by
  grind

private theorem yield_it_eq_inc (h : it.step.val = .yield it' idx) :
    it'.internalState.idx = it.internalState.idx + 1 := by
  grind

private theorem yield_valid [lawful : LawfulValid mk size valid] (h : it.step.val = .yield it' idx) :
    valid idx := by
  grind [lawful.valid]

private theorem done_idx_ge_size (h : it.step.val = .done) :
    it.internalState.idx ≥ size := by
  simp_all
  grind

end GenericIter

variable {aig : Aig}

section input

abbrev InputIterator (aig : Aig) := GenericIter InputIdx.ofIdx aig.numInputs (·.validIn aig)
instance {aig : Aig} : GenericIter.LawfulValid InputIdx.ofIdx aig.numInputs (·.validIn aig) where
  valid := by grind [InputIdx.validIn, numInputs]

/--
A forward iterator over inputs in the Aig.
-/
@[inline]
def inputIter (aig : Aig) : @Std.Iter (InputIterator aig) InputIdx :=
  ⟨⟨0⟩⟩

@[simp, grind =]
theorem length_inputIter_eq_numInputs :
    aig.inputIter.length = aig.numInputs := by
  simp [inputIter, GenericIter.length_eq_size_sub_idx]

@[simp, grind =]
theorem mem_inputIter_toList_iff_valid {idx : InputIdx} :
    idx ∈ aig.inputIter.toList ↔ idx.validIn aig := by
  grind [inputIter]

theorem inputIter_toList_ne_of_ne :
    ∀ {i j : Nat} (hi : i < aig.numInputs) (hj : j < aig.numInputs) (_ : i ≠ j),
      aig.inputIter.toList[i]'(by simpa) ≠ aig.inputIter.toList[j]'(by simpa) := by
  simp

end input

section latch

abbrev LatchIterator (aig : Aig) := GenericIter LatchIdx.ofIdx aig.numLatches (·.validIn aig)
instance {aig : Aig} : GenericIter.LawfulValid LatchIdx.ofIdx aig.numLatches (·.validIn aig) where
  valid := by grind [LatchIdx.validIn, numLatches]

/--
A forward iterator over latches in the Aig.
-/
@[inline]
def latchIter (aig : Aig) : @Std.Iter (LatchIterator aig) LatchIdx :=
  ⟨⟨0⟩⟩

@[simp, grind =]
theorem length_latchIter_eq_numLatches :
    aig.latchIter.length = aig.numLatches := by
  simp [latchIter, GenericIter.length_eq_size_sub_idx]

@[simp, grind =]
theorem mem_latchIter_toList_iff_valid {idx : LatchIdx} :
    idx ∈ aig.latchIter.toList ↔ idx.validIn aig := by
  grind [latchIter]

theorem latchIter_toList_ne_of_ne :
    ∀ {i j : Nat} (hi : i < aig.numLatches) (hj : j < aig.numLatches) (_ : i ≠ j),
      aig.latchIter.toList[i]'(by simpa) ≠ aig.latchIter.toList[j]'(by simpa) := by
  simp

end latch

/-
Forward iterators over variables
-/
section var

abbrev VarIterator (aig : Aig) := GenericIter Var.ofIdx aig.size (·.validIn aig)
instance {aig : Aig} : GenericIter.LawfulValid Var.ofIdx aig.size (·.validIn aig) where
  valid := by simp [Var.ext_idx, Var.validIn]

/--
A forward iterator over variables in the Aig.
-/
@[inline]
def iter (aig : Aig) : @Std.Iter (VarIterator aig) Var :=
  ⟨⟨0⟩⟩

@[simp, grind =]
theorem length_iter_eq_size :
    aig.iter.length = aig.size := by
  simp [iter, GenericIter.length_eq_size_sub_idx]

@[simp, grind =]
theorem mem_iter_toList_iff_valid {var : Var} :
    var ∈ aig.iter.toList ↔ var.validIn aig := by
  grind [iter]

@[simp, grind =]
theorem iter_toList_eq :
    aig.iter.toList = .ofFn (fun (n : Fin aig.size) => .ofIdx n) := by
  simp
  rw [length_iter_eq_size]
  grind [iter]

/--
Convenience function to access the current state of `Aig.iter`, which is guaranteed to
be the next returned value if the iterator is still valid.
-/
@[always_inline]
def _root_.Std.Iter.var (it : @Std.Iter (VarIterator aig) Var) : Var :=
  .ofIdx it.internalState.idx

variable {it it' : @Std.Iter (VarIterator aig) Var} {var : Var}

@[simp]
theorem length_eq_size_sub_var_idx :
    it.length = aig.size - it.var.idx := by
  simp [Std.Iter.var, GenericIter.length_eq_size_sub_idx]

@[simp, grind =]
theorem iter_var_eq_zero :
    aig.iter.var = .ofIdx 0 := by
  simp [iter, Std.Iter.var]

@[simp, grind .]
theorem iter_yield_eq_var (h : it.step.val = .yield it' var) :
    var = it.var := by
  grind only [Std.Iter.var, GenericIter.yield_idx_eq_internalState]

@[simp]
theorem iter_yield_var_eq_var_add_one (h : it.step.val = .yield it' var) :
    it'.var = it.var + 1 := by
  simp [Std.Iter.var, Var.ext_idx]
  grind only [GenericIter.yield_it_eq_inc]

grind_pattern iter_yield_var_eq_var_add_one => Std.IterStep.yield it' var, it.var

@[simp]
theorem iter_yield_validIn (h : it.step.val = .yield it' var) :
    var.validIn aig := by
  apply GenericIter.yield_valid h

grind_pattern iter_yield_validIn => Std.IterStep.yield it' var, var.validIn aig, it.step

@[simp]
theorem iter_done_var_ge_size (h : it.step.val = .done) :
    it.var.idx ≥ aig.size :=
  GenericIter.done_idx_ge_size h

grind_pattern iter_done_var_ge_size => it.step.val, Std.IterStep.done, it.var.idx

end var
