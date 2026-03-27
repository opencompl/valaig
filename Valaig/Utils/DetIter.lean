module

public import Init.Data.Iterators.Lemmas.Basic

public section
namespace Valaig.Utils

/--
A deterministic wrapper for non-monadic iterators (`Std.Iter`). These are by definition
deterministic, but may have an over approximate definition for `Std.Iterator.IsPlausibleStep`. This
wrapper defines `IsPlausibleStep` true iff the step is actually produced by the wrapped iterator.
This makes the plausibility definitions precise.

We provide a `forIn'` instance for any `Std.Iter` using this wrapper that provides a proof that
each element is in `it.toList`.
-/
structure DetIter (α β : Type w) where
  inner : @Std.Iter α β

namespace DetIter
variable {a β : Type w} {m : Type w -> Type w'}

@[local simp, local grind =]
theorem IterStep.mapIterator_eq {γ : Type w} {step : Std.IterStep α β} {f : α -> γ} :
    step.mapIterator f =
    match step with
    | .done => .done
    | .yield it' out => .yield (f it') out
    | .skip it' => .skip (f it') := by
  split <;> simp

@[local simp, local grind =]
theorem IterStep.successor_eq {step : Std.IterStep α β} :
    step.successor =
    match step with
    | .yield it' _
    | .skip it' => some it'
    | .done => none := by
  split <;> simp

@[always_inline]
def wrap : @Std.Iter α β -> @Std.Iter (DetIter α β) β :=
  Std.Iter.mk ∘ DetIter.mk

@[local simp, local grind =]
private theorem wrap_eq {it : @Std.Iter α β} :
    wrap it = (Std.Iter.mk ∘ DetIter.mk) it := by
  rfl

@[always_inline]
def wrapM : @Std.Iter α β -> @Std.IterM (DetIter α β) m β :=
  Std.IterM.mk ∘ DetIter.mk

@[local simp, local grind =]
private theorem wrapM_eq {it : @Std.Iter α β} :
    (wrapM it : Std.IterM m β) = (Std.IterM.mk ∘ DetIter.mk) it := by
  rfl

variable [Std.Iterator α Id β] [Pure m]

@[always_inline]
def step (it : @Std.IterM (DetIter α β) m β) : Std.IterStep (@Std.IterM (DetIter α β) m β) β :=
  it.internalState.inner.step.val.mapIterator wrapM

@[always_inline]
instance instIterator (α β : Type w) (m : Type w -> Type w') [Pure m] [Std.Iterator α Id β] :
    Std.Iterator (DetIter α β) m β where
  IsPlausibleStep it step := DetIter.step it = step
  step it := pure <| .deflate <| ⟨DetIter.step it, by rfl⟩

attribute [local ext, local grind ext] Std.Iter Std.IterM DetIter
attribute [local grind] Std.Iter.toIterM DetIter.step Std.Iter.IsPlausibleSuccessorOf
attribute [local grind =] Std.Iter.isPlausibleOutput_iff_exists
attribute [local grind =_] Std.Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM

theorem IsPlausibleStep_iff {it : @Std.IterM (DetIter α β) m β} {step} :
    it.IsPlausibleStep step ↔ DetIter.step it = step := by
  rfl

@[local grind =]
theorem IsPlausibleStep_iff_inner {it : @Std.IterM (DetIter α β) m β} {step} :
    it.IsPlausibleStep step ↔ step = it.internalState.inner.step.val.mapIterator wrapM := by
  simp only [IsPlausibleStep_iff]
  grind

theorem IsPlausibleStep_inner_of {it : @Std.IterM (DetIter α β) m β} {step} (h : it.IsPlausibleStep step) :
    it.internalState.inner.IsPlausibleStep (step.mapIterator (·.internalState.inner)) := by
  grind

@[local grind =]
theorem step_val_eq_inner {it : @Std.Iter (DetIter α β) β} :
    it.step.val = it.internalState.inner.step.val.mapIterator wrap := by
  grind

@[local grind =]
theorem IsPlausibleSuccessorOf_iff_inner_successor {it it' : @Std.IterM (DetIter α β) m β} :
    it'.IsPlausibleSuccessorOf it ↔ it.internalState.inner.step.val.successor = some it'.internalState.inner := by
  rw [Std.IterM.IsPlausibleSuccessorOf]
  constructor
  · grind
  · intro h
    exists it.internalState.inner.step.val.mapIterator wrapM
    grind

@[local grind =]
theorem IsPlausibleSuccessorOf_iff {it it' : @Std.Iter (DetIter α β) β} :
    it'.IsPlausibleSuccessorOf it ↔ it.step.val.successor = some it' := by
  grind

@[local grind .]
theorem IsPlausibleSuccessorOf_inner_of {it it' : @Std.IterM (DetIter α β) m β} (h : it'.IsPlausibleSuccessorOf it) :
    it'.internalState.inner.IsPlausibleSuccessorOf it.internalState.inner := by
  grind [Std.Iter.isPlausibleSuccessorOf_iff_exists]

@[local grind =]
theorem IsPlausibleOutput_iff_inner {it : @Std.IterM (DetIter α β) m β} {out : β} :
    it.IsPlausibleOutput out ↔ ∃ it', it.internalState.inner.step.val = (.yield it' out) := by
  simp only [Std.IterM.IsPlausibleOutput, IsPlausibleStep_iff_inner, IterStep.mapIterator_eq]
  split <;> simp <;> grind

@[local grind =]
theorem IsPlausibleOutput_iff [Std.Iterators.Finite α Id] {it : @Std.Iter (DetIter α β) β} {out : β} :
    it.IsPlausibleOutput out ↔ ∃ it', it.step.val = (.yield it' out) := by
  grind

theorem IsPlausibleOutput_inner_of {it : @Std.IterM (DetIter α β) m β} {out : β} (h : it.IsPlausibleOutput out) :
    it.internalState.inner.IsPlausibleOutput out := by
  grind

def myInstFinitenessRelation [Std.Iterators.Finite α Id] : Std.Iterators.FinitenessRelation (DetIter α β) m where
  Rel := InvImage Std.Iter.IsPlausibleSuccessorOf (·.internalState.inner)
  wf := InvImage.wf _ Std.Iterators.Finite.wf_of_id
  subrelation {it it'} h := by simp_wf; grind

instance [Std.Iterators.Finite α Id] : Std.Iterators.Finite (DetIter α β) m := by
  exact .of_finitenessRelation myInstFinitenessRelation

@[always_inline]
instance instIteratorLoop [Monad m] [Monad n] :
    Std.IteratorLoop (DetIter α β) m n :=
  .defaultImplementation

@[local grind =]
theorem IsPlausibleIndirectOutput_iff [Std.Iterators.Finite α Id] {it : @Std.Iter (DetIter α β) β} {out : β} :
    it.IsPlausibleIndirectOutput out ↔ out ∈ it.toList := by
  constructor
  · intro h
    induction h <;> grind [Std.Iter.toList_eq_match_step]
  · exact Std.Iter.isPlausibleIndirectOutput_of_mem_toList

@[local grind =]
theorem toList_eq_toList_inner [Std.Iterators.Finite α Id] {it : @Std.Iter (DetIter α β) β} :
    it.toList = it.internalState.inner.toList := by
  induction it using Std.Iter.inductSteps
  grind [Std.Iter.toList_eq_match_step]

@[expose]
def instMemToList : Membership β (@Std.Iter α β) where
  mem it out := out ∈ it.toList

@[simp, grind =]
theorem instMemToList_iff {it : @Std.Iter α β} {out : β} :
    instMemToList.mem it out ↔ out ∈ it.toList := by
  rfl

@[always_inline]
instance instForIn' [Monad n] [Std.Iterators.Finite α Id] :
    ForIn' n (@Std.Iter α β) β instMemToList where
  forIn' it init f :=
    Std.IteratorLoop.finiteForIn' (fun _ _ f c => f c.run)
      |>.forIn' (wrap it).toIterM init
        fun out h acc => f out (by grind) acc

end DetIter
