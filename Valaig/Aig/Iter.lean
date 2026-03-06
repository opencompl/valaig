module

public import Init.Data.Iterators.Lemmas.Monadic.Basic
public import Init.Data.Iterators.Lemmas.Basic

public section
namespace Valaig.Aig

/--
A generic iterator that forward iterates over a consecutive range of valid indices. This
is specialised to produce input/latch indices and variables.

This expects an instance of `Iter.Lawful` for `inc` and `valid` for full reasoning
abilities.
-/
structure Iter {α : Type} (inc : α -> α) (valid : α -> Prop) (toNat : α -> Nat) (ofNat : Nat -> α) (size : Nat) where
  idx : α

namespace Iter

class Lawful {α : Type} (inc : α -> α) (valid : α -> Prop) (toNat : α -> Nat) (ofNat : Nat -> α) (size : Nat) where
  ofNat_toNat (idx : α) : ofNat (toNat idx) = idx := by grind
  toNat_ofNat (idx : Nat) : toNat (ofNat idx) = idx := by grind
  consecutive (idx : α) : toNat (inc idx) = toNat idx + 1 := by grind
  max (idx : α) : valid idx ↔ toNat idx < size := by grind

variable {α : Type} {inc : α -> α} {valid : α -> Prop}
variable {toNat : α -> Nat} {ofNat : Nat -> α} {size : Nat}
variable [DecidablePred valid] {out : α}
variable {m : Type -> Type _} [Pure m] {n : Type _ -> Type _}

/--
Construct a new iterator from the 0th index
-/
@[always_inline]
def init : Iter inc valid toNat ofNat size :=
  ⟨ofNat 0⟩

@[always_inline]
instance instIterator : Std.Iterator (Iter inc valid toNat ofNat size) m α where
  IsPlausibleStep it step :=
    let idx := it.internalState.idx
    match step with
    | .yield it' out => valid idx ∧ it'.internalState.idx = inc idx ∧ out = idx
    | .skip _ => False
    | .done => ¬valid idx

  step it := pure <| .deflate <|
    let s := it.internalState
    if h : valid s.idx then
      .yield ⟨⟨inc s.idx⟩⟩ s.idx (by grind)
    else
      .done (by grind)

/-
These theorems are mainly private and for establishing the correctness of the typeclasses
-/
variable {it it' : @Std.Iter (Iter inc valid toNat ofNat size) α}
variable {itm itm' : @Std.IterM (Iter inc valid toNat ofNat size) m α}

@[local simp, local grind =]
private theorem IsPlausibleStep_iff {step} :
    itm.IsPlausibleStep step ↔
    if valid itm.internalState.idx then
      step = .yield ⟨⟨inc itm.internalState.idx⟩⟩ itm.internalState.idx
    else
      step = .done := by
  simp only [Std.IterM.IsPlausibleStep, Std.Iterator.IsPlausibleStep, instIterator]
  grind only [Iter, Std.IterM]

@[local simp, local grind =]
private theorem IsPlausibleStep_iff' {step} :
    it.IsPlausibleStep step ↔
    if valid it.internalState.idx then
      step = .yield ⟨⟨inc it.internalState.idx⟩⟩ it.internalState.idx
    else
      step = .done := by
  simp only [Std.Iter.IsPlausibleStep, Std.IterStep.mapIterator, Std.Iter.toIterM, Std.IterM.IsPlausibleStep, Std.Iterator.IsPlausibleStep, instIterator]
  grind only [Iter, Std.Iter]

@[local simp, local grind =]
private theorem IsPlausibleOutput_iff {out : α} :
    itm.IsPlausibleOutput out ↔
      valid itm.internalState.idx ∧ out = itm.internalState.idx := by
  simp [Std.IterM.IsPlausibleOutput]

omit [Pure m] in
@[local simp, local grind =]
private theorem successor_eq {step : Std.IterStep (@Std.IterM β m α) α} :
    step.successor =
    match step with
    | .yield itm _ => some itm
    | .skip itm => some itm
    | .done => none := by
  grind [Std.IterStep.successor_yield, Std.IterStep.successor_skip, Std.IterStep.successor_done]

@[local simp, local grind =]
private theorem IsPlausibleSuccessorOf_iff :
    itm'.IsPlausibleSuccessorOf itm ↔
      valid itm.internalState.idx ∧
      itm'.internalState.idx = inc itm.internalState.idx := by
  constructor
  · grind [Std.IterM.IsPlausibleSuccessorOf]
  · grind [Iter, Std.IterM, Std.IterM.isPlausibleSuccessorOf_of_yield (out := itm.internalState.idx)]

open Std.Iterators in
private def instFinitenessRelation [lawful : Lawful inc valid toNat ofNat size] : FinitenessRelation (Iter inc valid toNat ofNat size) m where
  Rel := InvImage WellFoundedRelation.rel (size - toNat ·.internalState.idx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation h := by simp_wf; grind [lawful.max, lawful.consecutive]

instance instFinite [Lawful inc valid toNat ofNat size] : Std.Iterators.Finite (Iter inc valid toNat ofNat size) m := by
  exact .of_finitenessRelation instFinitenessRelation

@[always_inline]
instance instIteratorLoop [Monad m] [Monad n] :
    Std.IteratorLoop (Iter inc valid toNat ofNat size) m n :=
  .defaultImplementation

@[local grind .]
private theorem IsPlausibleIndirectOutput_valid {out : α} (h : itm.IsPlausibleIndirectOutput out) :
    valid out := by
  induction h <;> grind

@[always_inline]
instance instForIn' [Monad n] :
    ForIn' n (@Std.Iter (Iter inc valid toNat ofNat size) α) α ⟨fun _ out => valid out⟩ where
  forIn' it init f :=
    Std.IteratorLoop.finiteForIn' (fun _ _ f c => f c.run) |>.forIn' it.toIterM init
      fun out h acc => f out (by grind) acc

/--
Convenience function to access the current state of the iterator, which is guaranteed to
be the next returned value if the iterator is still valid.
-/
@[always_inline, local simp, local grind]
def _root_.Std.Iter.val (it : @Std.Iter (Iter inc valid toNat ofNat size) α) : α :=
  it.internalState.idx

@[local grind =]
theorem length_eq_size_sub_val [lawful : Lawful inc valid toNat ofNat size] :
    it.length = size - toNat it.val := by
  induction it using Std.Iter.inductSteps with | step it ihy _ =>
  grind [Std.Iter.length_eq_match_step, lawful.consecutive, lawful.max]

omit [DecidablePred valid] in
@[simp, grind! .]
theorem val_init :
    (⟨init⟩ : @Std.Iter (Iter inc valid toNat ofNat size) α).val = ofNat 0 := by
  rfl

@[simp, grind! .]
theorem length_init [lawful : Lawful inc valid toNat ofNat size] :
    (⟨init⟩ : @Std.Iter (Iter inc valid toNat ofNat size) α).length = size := by
  grind [lawful.toNat_ofNat]

@[simp, grind .]
theorem IsPlausibleStep_skip :
    ¬it.IsPlausibleStep (.skip it') := by
  simp

@[simp, grind .]
theorem step_eq_iff_IsPlausibleStep {step} :
    it.step.val = step ↔ it.IsPlausibleStep step := by
  grind

variable [lawful : Lawful inc valid toNat ofNat size]

@[simp]
theorem length_yield (h : it.IsPlausibleStep (.yield it' out)) :
    it'.length = it.length - 1 := by
  grind [lawful.consecutive]

@[simp]
theorem length_yield_gt_zero (h : it.IsPlausibleStep (.yield it' out)) :
    it.length > 0 := by
  grind [lawful.max]

@[simp]
theorem length_yield' (h : it.IsPlausibleStep (.yield it' out)) :
    it'.length + 1 = it.length := by
  grind [length_yield, length_yield_gt_zero]

grind_pattern length_yield' => it.IsPlausibleStep (.yield it' out), it'.length

@[simp]
theorem length_done (h : it.IsPlausibleStep .done) :
    it.length = 0 := by
  grind [lawful.max]

grind_pattern length_done => it.IsPlausibleStep .done, it.length

@[simp]
theorem length_zero_done (h : it.length = 0) :
    it.step.val = .done := by
  grind [lawful.max]

@[simp, grind .]
theorem length_le_size :
    it.length ≤ size := by
  grind

@[local grind =]
theorem toList_eq_ofFn :
    it.toList = List.ofFn (fun (n : Fin it.length) => ofNat (toNat it.val + n)) := by
  induction it using Std.Iter.inductSteps with | step it ihy _ =>
  rw [Std.Iter.toList_eq_match_step] 
  split
  · apply List.ext_getElem
    · grind [lawful.consecutive, lawful.max]
    · simp [List.getElem_cons]
      intros
      split
      · simp_all only
        grind [lawful.ofNat_toNat]
      · grind [lawful.consecutive, lawful.max]
  · grind
  · grind

@[simp, grind =]
theorem toList_eq_ofFn' (h : it.val = ofNat 0) :
    it.toList = List.ofFn (fun (n : Fin it.length) => ofNat n) := by
  grind [lawful.toNat_ofNat]

@[simp, grind =]
theorem mem_init_toList_iff_valid {idx : α} :
    idx ∈ (⟨init⟩ : @Std.Iter (Iter inc valid toNat ofNat size) α).toList ↔ valid idx := by
  rw [toList_eq_ofFn']
  simp
  constructor
  · grind [lawful.max, lawful.toNat_ofNat]
  · intro valid
    exists ⟨toNat idx, by grind [lawful.max, lawful.toNat_ofNat]⟩
    grind [lawful.ofNat_toNat, lawful.max, lawful.toNat_ofNat]
  · grind

@[simp]
theorem toList_done (h : it.IsPlausibleStep .done) :
    it.toList = [] := by
  grind

grind_pattern toList_done => it.IsPlausibleStep .done, it.toList

theorem toList_yield (h : it.IsPlausibleStep (.yield it' out)) :
    it.toList = out :: it'.toList := by
  induction h : it.toList with
  | nil => grind [List.ofFn_eq_nil_iff, lawful.max]
  | cons out' tail ih => grind [Std.Iter.toList_eq_match_step]

grind_pattern toList_yield => it.IsPlausibleStep (.yield it' out), it.toList

omit lawful in
@[simp, grind .]
theorem yield_eq_val (h : it.IsPlausibleStep (.yield it' out)) :
    it.val = out := by
  grind

omit lawful in
@[simp, grind .]
theorem valid_yield (h : it.IsPlausibleStep (.yield it' out)) :
    valid out := by
  grind

@[simp, grind .]
theorem val_yield (h : it.IsPlausibleStep (.yield it' out)) :
    toNat it'.val = toNat it.val + 1 := by
  grind [lawful.consecutive]

@[simp]
theorem val_done (h : it.IsPlausibleStep .done) :
    toNat it.val ≥ size := by
  grind [lawful.max]

grind_pattern val_done => it.IsPlausibleStep .done, it.val
