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
  hvalid : ∀ {out : α}, valid out ↔ ∃ (n : Nat) (_ : out = mk n), n < size

universe u
variable {α : Type} {mk : Nat -> α} {size : Nat} {valid : α -> Prop}
variable {m : Type -> Type u} [Pure m]

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
attribute [local grind unfold] Std.PlausibleIterStep.yield Std.PlausibleIterStep.skip Std.PlausibleIterStep.done
attribute [local grind =] Std.IterStep.successor_yield Std.IterStep.successor_skip Std.IterStep.successor_done
attribute [local grind =] Std.IterStep.mapIterator_yield
attribute [local simp, local grind unfold] Std.Iterator.step Std.Iter.step Std.IterM.step
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

variable {it : @Std.Iter (GenericIter mk size valid) α} {out : α}

@[simp, grind =]
theorem IsPlausibleOutput_iff :
    it.IsPlausibleOutput out ↔
      it.internalState.idx < size ∧ out = mk it.internalState.idx := by
  simp
  intros
  exists ⟨⟨it.internalState.idx + 1⟩⟩

@[simp, grind =]
theorem IsPlausibleSuccessorOf_iff {it' : @Std.Iter (GenericIter mk size valid) α} :
    it'.IsPlausibleSuccessorOf it ↔
      it.internalState.idx < size ∧
      it'.internalState.idx = it.internalState.idx + 1 := by
  constructor
  · grind [Std.Iter.IsPlausibleSuccessorOf]
  · rw [Std.Iter.isPlausibleSuccessorOf_iff_exists]
    intro h
    exists .yield ⟨⟨it.internalState.idx + 1⟩⟩ (mk it.internalState.idx)
    constructor
    · simp
      congr
      grind
    · grind

@[simp, grind =]
theorem IsPlausibleIndirectOutput_iff :
    it.IsPlausibleIndirectOutput out ↔
      ∃ (n : Nat) (_ : n < size) (_ : n ≥ it.internalState.idx), mk n = out := by
  constructor
  · intro h
    induction h <;> grind
  · rintro ⟨n, h1, h2, h3⟩
    induction h : (size - it.internalState.idx) generalizing it
    case zero => grind
    case succ n' ih =>
      by_cases n = it.internalState.idx
      · grind
      · let it' := it.step.val.successor.get <| by grind
        apply Std.Iter.IsPlausibleIndirectOutput.indirect (it' := it')
        · grind
        · apply ih <;> grind

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
      fun out h acc => f out (by grind [lawful.hvalid]) acc

end GenericIter

abbrev InputIterator (aig : Aig) := GenericIter InputIdx.ofIdx aig.numInputs (·.validIn aig)
instance {aig : Aig} : GenericIter.LawfulValid InputIdx.ofIdx aig.numInputs (·.validIn aig) where
  hvalid := by grind [InputIdx.validIn, numInputs]

/--
A forward iterator over inputs in the Aig.
-/
@[inline]
def inputIter (aig : Aig) : @Std.Iter (InputIterator aig) InputIdx :=
  ⟨⟨0⟩⟩

abbrev LatchIterator (aig : Aig) := GenericIter LatchIdx.ofIdx aig.numLatches (·.validIn aig)
instance {aig : Aig} : GenericIter.LawfulValid LatchIdx.ofIdx aig.numLatches (·.validIn aig) where
  hvalid := by grind [LatchIdx.validIn, numLatches]

/--
A forward iterator over latches in the Aig.
-/
@[inline]
def latchIter (aig : Aig) : @Std.Iter (LatchIterator aig) LatchIdx :=
  ⟨⟨0⟩⟩

abbrev VarIterator (aig : Aig) := GenericIter Var.ofIdx aig.size (·.validIn aig)
instance {aig : Aig} : GenericIter.LawfulValid Var.ofIdx aig.size (·.validIn aig) where
  hvalid := by grind [Var.validIn]

/--
A forward iterator over variables in the Aig.
-/
@[inline]
def iter (aig : Aig) : @Std.Iter (VarIterator aig) Var :=
  ⟨⟨0⟩⟩
