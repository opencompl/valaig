module

public import Valaig.Aig.Basic
import all Valaig.Aig.Basic
import Valaig.Utils.GrindIter
import Valaig.Utils.DetIter

public section
namespace Valaig.Aig
variable {aig : Aig}

/--
A custom iterator type for the forward iteration of variables that is easy to reason about.
-/
structure VarIter (aig : Aig) where
  var : Var
  range : var.validIn aig ∨ var.idx = aig.size := by grind

/--
A forward iterator over variables in the Aig. See also `iterVal`.
-/
@[inline]
def iter (aig : Aig) : @Std.Iter aig.VarIter Var :=
  ⟨.ofIdx 0, by grind [Var.validIn_iff]⟩

/--
The next value to be returned by a variable iterator, or `Var.ofIdx aig.size` if the iterator is
done.
-/
@[inline]
def iterVal (aig : Aig) (it : @Std.Iter aig.VarIter Var) : Var :=
  it.internalState.var

namespace VarIter

variable {m : Type -> Type _} [Pure m] {n : Type _ -> Type _}

attribute [local grind =] Var.validIn_iff
attribute [local ext, local grind ext] Std.Iter Std.IterM VarIter
attribute [local grind =] Utils.DetIter.IterStep.mapIterator_eq Utils.DetIter.IterStep.successor_eq
attribute [local grind] Std.Iter.toIterM

@[always_inline, local grind]
def step (it : @Std.IterM aig.VarIter m Var) : Std.IterStep (@Std.IterM aig.VarIter m Var) Var :=
  let var := it.internalState.var
  if h : var.validIn aig then
    .yield ⟨⟨var + 1, by grind⟩⟩ var
  else
    .done

@[always_inline]
instance instIterator : Std.Iterator aig.VarIter m Var where
  IsPlausibleStep it step :=
    let var := it.internalState.var
    match step with
    | .done => var.idx = aig.size
    | .yield it' out => it'.internalState.var = var + 1 ∧ out = var
    | .skip _ => False

  step it := pure <| .deflate <| ⟨step it, by grind [VarIter.range]⟩

@[simp, local grind =]
theorem IsPlausibleStep_iff {it : @Std.IterM aig.VarIter m Var} {step} :
    it.IsPlausibleStep step ↔ VarIter.step it = step := by
  simp only [Std.IterM.IsPlausibleStep, Std.Iterator.IsPlausibleStep, instIterator, VarIter.step]
  grind

@[simp, local grind =]
theorem IsPlausibleSuccessorOf_iff {it it' : @Std.IterM aig.VarIter m Var} :
    it'.IsPlausibleSuccessorOf it ↔ (step it).successor = some it' := by
  grind [Std.IterM.IsPlausibleSuccessorOf]

open Std.Iterators in
private def instFinitenessRelation : FinitenessRelation aig.VarIter m where
  Rel := InvImage WellFoundedRelation.rel (aig.size - ·.internalState.var.idx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation h := by simp_wf; grind

instance instFinite : Std.Iterators.Finite aig.VarIter m := by
  exact .of_finitenessRelation instFinitenessRelation

@[always_inline]
instance instIteratorLoop [Monad m] [Monad n] : Std.IteratorLoop aig.VarIter m n :=
  .defaultImplementation

variable {it it' : @Std.Iter aig.VarIter Var}

@[simp, grind .]
theorem IsPlausibleStep_skip:
    ¬it.IsPlausibleStep (.skip it') := by
  grind [step]

@[simp, grind .]
theorem step_eq_iff_IsPlausibleStep {step} :
    it.step.val = step ↔ it.IsPlausibleStep step := by
  grind

@[local simp, local grind =]
private theorem iterVal_eq_inner :
    aig.iterVal it = it.internalState.var := by
  grind [iterVal]

@[local grind =]
theorem length_eq_size_sub_iterVal :
    it.length = aig.size - (aig.iterVal it).idx := by
  induction it using Std.Iter.inductSteps with | step it ihy _ =>
  grind [Std.Iter.length_eq_match_step]

grind_pattern length_eq_size_sub_iterVal => it.length, aig.size - (aig.iterVal it).idx

@[simp]
theorem length_done (h : it.IsPlausibleStep .done) :
    it.length = 0 := by
  grind

grind_pattern length_done => it.IsPlausibleStep .done, it.length

@[simp]
theorem length_zero_done (h : it.length = 0) :
    it.step.val = .done := by
  grind

grind_pattern length_zero_done => it.length, it.step

@[simp]
theorem length_yield (h : it.IsPlausibleStep (.yield it' out)) :
    it'.length = it.length - 1 := by
  grind

@[simp]
theorem length_yield_gt_zero (h : it.IsPlausibleStep (.yield it' out)) :
    it.length > 0 := by
  grind

@[simp]
theorem length_yield' (h : it.IsPlausibleStep (.yield it' out)) :
    it'.length + 1 = it.length := by
  grind

grind_pattern length_yield' => it.IsPlausibleStep (.yield it' out), it.length
grind_pattern length_yield' => it.IsPlausibleStep (.yield it' out), it'.length

@[simp, grind .]
theorem length_le_size :
    it.length ≤ aig.size := by
  grind

@[simp]
theorem iterVal_done (h : it.IsPlausibleStep .done) :
    aig.iterVal it = .ofIdx aig.size := by
  grind

grind_pattern iterVal_done => it.IsPlausibleStep .done, aig.iterVal it

@[simp]
theorem iterVal_yield (h : it.IsPlausibleStep  (.yield it' out)) :
    aig.iterVal it' = aig.iterVal it + 1 := by
  grind

grind_pattern iterVal_yield => it.IsPlausibleStep (.yield it' out), aig.iterVal it

@[simp]
theorem out_yield (h : it.IsPlausibleStep (.yield it' out)) :
    out = aig.iterVal it := by
  grind

grind_pattern out_yield => it.IsPlausibleStep (.yield it' out), aig.iterVal it
grind_pattern out_yield => it.IsPlausibleStep (.yield it' out), aig.iterVal it'

@[simp]
theorem iterVal_validIn_done (h : it.IsPlausibleStep .done) :
    ¬(aig.iterVal it).validIn aig := by
  grind

grind_pattern iterVal_validIn_done => it.IsPlausibleStep .done, (aig.iterVal it).validIn aig

@[simp]
theorem iterVal_validIn_yield (h : it.IsPlausibleStep (.yield it' out)) :
    (aig.iterVal it).validIn aig := by
  grind

grind_pattern iterVal_validIn_yield => it.IsPlausibleStep (.yield it' out), (aig.iterVal it).validIn aig

@[simp]
theorem validIn_yield (h : it.IsPlausibleStep (.yield it' out)) :
    out.validIn aig := by
  grind

grind_pattern validIn_yield => it.IsPlausibleStep (.yield it' out), out.validIn aig

@[local grind =]
theorem toList_eq_ofFn :
    it.toList = List.ofFn (fun (n : Fin it.length) => aig.iterVal it + n.val) := by
  induction it using Std.Iter.inductSteps with | step it ihy _ =>
  rw [Std.Iter.toList_eq_match_step] 
  apply List.ext_getElem <;> grind

@[simp]
theorem toList_done (h : it.IsPlausibleStep .done) :
    it.toList = [] := by
  grind

grind_pattern toList_done => it.IsPlausibleStep .done, it.toList

theorem toList_yield (h : it.IsPlausibleStep (.yield it' out)) :
    it.toList = out :: it'.toList := by
  induction h : it.toList with
  | nil => grind [List.ofFn_eq_nil_iff]
  | cons out' tail ih => grind [Std.Iter.toList_eq_match_step]

grind_pattern toList_yield => it.IsPlausibleStep (.yield it' out), it.toList

end VarIter

attribute [local simp, local grind =] VarIter.iterVal_eq_inner

@[simp, grind =]
theorem idx_iterVal_iter :
    (aig.iterVal aig.iter).idx = 0 := by
  grind [iter]

@[simp, grind =]
theorem iterVal_iter :
    aig.iterVal aig.iter = .constant := by
  grind

@[simp, grind =]
theorem length_iter :
    aig.iter.length = aig.size := by
  grind [VarIter.length_eq_size_sub_iterVal]

@[grind =]
theorem toList_iter :
    aig.iter.toList = List.ofFn (fun (n : Fin aig.size) => .ofIdx n) := by
  apply List.ext_getElem
  · grind
  · grind [iter, VarIter.toList_eq_ofFn]

@[simp, grind =]
theorem mem_iter_iff {var : Var} :
    var ∈ aig.iter.toList ↔ var.validIn aig := by
  simp only [toList_iter, List.mem_ofFn]
  constructor
  · grind [Var.validIn_iff]
  · intro h
    exists ⟨var.idx, by grind⟩

/--
A forward iterator over inputs in the Aig.
-/
@[inline]
def inputs (aig : Aig) :=
  aig._inputs.iter.map InputIdx.ofIdx

@[simp, grind =]
theorem length_inputs :
    aig.inputs.length = aig.numInputs := by
  grind [inputs, numInputs]

theorem length_toList_inputs :
    aig.inputs.toList.length = aig.numInputs := by
  grind

@[simp, grind =]
theorem mem_inputs_iff {idx : InputIdx} :
    idx ∈ aig.inputs.toList ↔ idx.validIn aig := by
  grind [inputs, InputIdx.validIn]

@[simp, grind .]
theorem nodup_toList_inputs :
    aig.inputs.toList.Nodup := by
  grind [inputs, List.pairwise_iff_getElem]

theorem distinct_toList_inputs {idx idx' : Nat} (h : idx < aig.inputs.length) (h' : idx' < aig.inputs.length)
    (diff : idx ≠ idx') :
      aig.inputs.toList[idx] ≠ aig.inputs.toList[idx'] := by
  grind [@nodup_toList_inputs aig, List.pairwise_iff_getElem]

grind_pattern distinct_toList_inputs => aig.inputs.toList[idx], aig.inputs.toList[idx'] where
  idx =/= idx'

theorem Perm_inputs_iff_validIn {aig aig' : Aig} :
    aig'.inputs.toList.Perm aig.inputs.toList ↔
    ∀ (idx : InputIdx), idx.validIn aig' ↔ idx.validIn aig := by
  constructor
  · grind [=_ mem_inputs_iff, List.Perm.mem_iff]
  · grind [List.Nodup.count]

theorem numInputs_eq_of_validIn_eq {aig aig' : Aig} (h : ∀ (idx : InputIdx), idx.validIn aig' ↔ idx.validIn aig) :
    aig'.numInputs = aig.numInputs := by
  grind [=_ length_toList_inputs, Perm_inputs_iff_validIn, List.Perm.length_eq]

/--
A forward iterator over latches in the Aig.
-/
@[inline]
def latches (aig : Aig) :=
  aig._latches.iter.map LatchIdx.ofIdx

@[simp, grind =]
theorem length_latches :
    aig.latches.length = aig.numLatches := by
  grind [latches, numLatches]

theorem length_toList_latches :
    aig.latches.toList.length = aig.numLatches := by
  grind

@[simp, grind =]
theorem mem_latches_iff {idx : LatchIdx} :
    idx ∈ aig.latches.toList ↔ idx.validIn aig := by
  grind [latches, LatchIdx.validIn]

@[simp, grind .]
theorem nodup_toList_latches :
    aig.latches.toList.Nodup := by
  grind [latches, List.pairwise_iff_getElem]

theorem distinct_toList_latches {idx idx' : Nat} (h : idx < aig.latches.length) (h' : idx' < aig.latches.length)
    (diff : idx ≠ idx') :
      aig.latches.toList[idx] ≠ aig.latches.toList[idx'] := by
  grind [@nodup_toList_latches aig, List.pairwise_iff_getElem]

grind_pattern distinct_toList_latches => aig.latches.toList[idx], aig.latches.toList[idx'] where
  idx =/= idx'

theorem Perm_latches_iff_validIn {aig aig' : Aig} :
    aig'.latches.toList.Perm aig.latches.toList ↔
    ∀ (idx : LatchIdx), idx.validIn aig' ↔ idx.validIn aig := by
  constructor
  · grind [=_ mem_latches_iff, List.Perm.mem_iff]
  · grind [List.Nodup.count]

theorem numLatches_eq_of_validIn_eq {aig aig' : Aig} (h : ∀ (idx : LatchIdx), idx.validIn aig' ↔ idx.validIn aig) :
    aig'.numLatches = aig.numLatches := by
  grind [=_ length_toList_latches, Perm_latches_iff_validIn, List.Perm.length_eq]
