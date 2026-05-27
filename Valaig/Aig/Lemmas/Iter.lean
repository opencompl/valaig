module

import all Valaig.Aig.Basic
public import Valaig.Aig.Basic
import Valaig.Aig.Lemmas.Monotone
import Valaig.Aig.Lemmas.Basic
import Valaig.ForLean.Iter
import Init.Data.Iterators.Lemmas.Basic

public section
namespace Valaig.Aig
variable {aig : Aig}

/-
  `iter`/`iterVal`/`iterEnd`.
-/

section iter
namespace VarIter

variable {m : Type -> Type _} [Pure m]

attribute [local ext, local grind ext] Std.Iter Std.IterM VarIter
attribute [local grind] Std.Iter.toIterM step iterVal iterEnd
attribute [local grind =] IsPlausibleStep_iff IsPlausibleSuccessorOf_iff

variable {it it' : @Std.Iter aig.VarIter Var}

@[simp, grind .]
theorem IsPlausibleStep_skip:
    ¬it.IsPlausibleStep (.skip it') := by
  grind

@[simp, grind norm]
theorem step_eq_IsPlausibleStep {step} :
    it.step.val = step ↔ it.IsPlausibleStep step := by
  grind

@[local simp, local grind =]
private theorem iterVal_eq :
    aig.iterVal it = it.internalState.var := by
  grind

@[local grind =]
theorem length_eq_size_sub_iterVal :
    it.length = aig.size - (aig.iterVal it).idx := by
  induction it using Std.Iter.inductSteps with | step it ihy _ =>
  rw [Std.Iter.length_eq_match_step]
  split <;> grind

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

@[simp, grind .]
theorem length_yield' (h : it.IsPlausibleStep (.yield it' out)) :
    it'.length + 1 = it.length := by
  grind

@[simp, grind .]
theorem length_le_size :
    it.length ≤ aig.nodes.size := by
  grind

@[grind →]
theorem done_eq (h : it.IsPlausibleStep .done) :
    it = aig.iterEnd := by
  grind

@[simp, grind .]
theorem iterVal_yield (h : it.IsPlausibleStep  (.yield it' out)) :
    aig.iterVal it' = aig.iterVal it + 1 := by
  grind

@[grind →]
theorem out_yield (h : it.IsPlausibleStep (.yield it' out)) :
    out = aig.iterVal it := by
  grind

@[simp, grind .]
theorem iterVal_yield_mem_nodes (h : it.IsPlausibleStep (.yield it' out)) :
    (aig.iterVal it) ∈ aig.nodes := by
  grind

@[local grind =]
theorem toList_eq_ofFn :
    it.toList = List.ofFn (fun (n : Fin it.length) => aig.iterVal it + n.val) := by
  induction it using Std.Iter.inductSteps with | step it ihy _ =>
  rw [Std.Iter.toList_eq_match_step] 
  apply List.ext_getElem <;> split <;> grind

@[simp]
theorem toList_done (h : it.IsPlausibleStep .done) :
    it.toList = [] := by
  grind

grind_pattern toList_done => it.IsPlausibleStep .done, it.toList

theorem toList_yield (h : it.IsPlausibleStep (.yield it' out)) :
    it.toList = out :: it'.toList := by
  induction h : it.toList with
  | nil => grind [List.ofFn_eq_nil_iff]
  | cons out' tail ih =>
    rw [Std.Iter.toList_eq_match_step]
    apply List.ext_getElem <;> split <;> grind

grind_pattern toList_yield => it.IsPlausibleStep (.yield it' out), it.toList

@[simp, grind =]
theorem step_iterEnd :
    aig.iterEnd.step.val = .done := by
  grind

@[simp, grind .]
theorem iterVal_le_nextVar :
    aig.iterVal it ≤ aig.nextVar := by
  grind

@[simp, grind =]
theorem mem_nodes_iff_not_iterEnd :
    (aig.iterVal it) ∈ aig.nodes ↔ it ≠ aig.iterEnd := by
  grind

end VarIter

attribute [local simp, local grind =] VarIter.iterVal_eq

@[simp, grind =]
theorem iterVal_iter :
    aig.iterVal aig.iter = .constant := by
  grind [iter, iterVal]

@[simp, grind =]
theorem iterVal_iterEnd :
    aig.iterVal aig.iterEnd = aig.nextVar := by
  grind [iterEnd, iterVal]

@[simp, grind =]
theorem length_iter :
    aig.iter.length = aig.nodes.size := by
  grind [VarIter.length_eq_size_sub_iterVal]

@[simp, grind =]
theorem length_toList_iter :
    aig.iter.toList.length = aig.nodes.size := by
  grind

@[grind =]
theorem toList_iter :
    aig.iter.toList = List.ofFn (fun (n : Fin aig.size) => .ofIdx n) := by
  apply List.ext_getElem
  · grind
  · grind [iter, VarIter.toList_eq_ofFn]

@[simp, grind =]
theorem mem_iter {var : Var} :
    var ∈ aig.iter.toList ↔ var ∈ aig.nodes := by
  simp only [toList_iter, List.mem_ofFn]
  constructor
  · grind [validIn_iff]
  · intro h
    exists ⟨var.idx, by grind⟩

@[grind =]
theorem toArray_iter :
    aig.iter.toArray = aig.iter.toList.toArray := by
  grind

@[simp, grind .]
theorem nodup_toList_iter :
    aig.iter.toList.Nodup := by
  grind [iter, List.pairwise_iff_getElem]

theorem distinct_toList_iter {idx idx' : Nat} (h : idx < aig.iter.length) (h' : idx' < aig.iter.length)
    (diff : idx ≠ idx') :
      aig.iter.toList[idx] ≠ aig.iter.toList[idx'] := by
  grind [@nodup_toList_iter aig, List.pairwise_iff_getElem]

grind_pattern distinct_toList_iter => aig.iter.toList[idx], aig.iter.toList[idx'] where
  idx =/= idx'

theorem Perm_iter_iff {aig aig' : Aig} :
    aig'.iter.toList.Perm aig.iter.toList ↔
    ∀ (var : Var), var ∈ aig'.nodes ↔ var ∈ aig.nodes := by
  constructor
  · grind [=_ mem_iter, List.Perm.mem_iff]
  · grind [List.Nodup.count]

theorem size_nodes_eq_of_mem_nodes_eq {aig aig' : Aig} (h : ∀ (var : Var), var ∈ aig'.nodes ↔ var ∈ aig.nodes) :
    aig'.nodes.size = aig.nodes.size := by
  grind [=_ length_toList_iter, Perm_iter_iff, List.Perm.length_eq]

@[simp]
theorem toList_iter_prefix_mono {old new : Aig} (mono : old ≤ new):
    old.iter.toList <+: new.iter.toList := by
  grind [List.prefix_iff_getElem]

end iter

/-
  `inputsIter`.
-/
section inputsIter
attribute [local simp, local grind] inputsIter

@[simp, grind =]
theorem length_inputsiter :
    aig.inputsIter.length = aig.inputs.size := by
  grind [inputs]

@[simp, grind =]
theorem length_toList_inputsIter :
    aig.inputsIter.toList.length = aig.inputs.size := by
  grind

@[simp, grind =]
theorem mem_inputsIter {idx : InputIdx} :
    idx ∈ aig.inputsIter.toList ↔ idx ∈ aig.inputs := by
  grind [inputs]

@[grind =]
theorem toArray_inputsIter :
    aig.inputsIter.toArray = aig.inputsIter.toList.toArray := by
  grind

@[simp, grind .]
theorem nodup_inputsIter :
    aig.inputsIter.toList.Nodup := by
  grind [List.pairwise_iff_getElem]

theorem distinct_inputsIter {idx idx' : Nat} (h : idx < aig.inputsIter.length) (h' : idx' < aig.inputsIter.length)
    (diff : idx ≠ idx') :
      aig.inputsIter.toList[idx] ≠ aig.inputsIter.toList[idx'] := by
  grind [@nodup_inputsIter aig, List.pairwise_iff_getElem]

grind_pattern distinct_inputsIter => aig.inputsIter.toList[idx], aig.inputsIter.toList[idx'] where
  idx =/= idx'

theorem Perm_inputsIter_iff {aig aig' : Aig} :
    aig'.inputsIter.toList.Perm aig.inputsIter.toList ↔
    ∀ (idx : InputIdx), idx ∈ aig'.inputs ↔ idx ∈ aig.inputs := by
  constructor
  · grind [=_ mem_inputsIter, List.Perm.mem_iff]
  · grind [List.Nodup.count]

theorem size_inputs_eq_of_mem_inputs_eq {aig aig' : Aig} (h : ∀ (idx : InputIdx), idx ∈ aig'.inputs ↔ idx ∈ aig.inputs) :
    aig'.inputs.size = aig.inputs.size := by
  grind [=_ length_toList_inputsIter, Perm_inputsIter_iff, List.Perm.length_eq]

@[simp]
theorem toList_inputsIter_subset_mono {old new : Aig} (mono : old ≤ new) :
    old.inputsIter.toList ⊆ new.inputsIter.toList := by
  grind

end inputsIter

/-
  `latchesIter`.
-/
section latchesIter
attribute [local simp, local grind] latchesIter

@[simp, grind =]
theorem length_latchesiter :
    aig.latchesIter.length = aig.latches.size := by
  grind [latches]

@[simp, grind =]
theorem length_toList_latchesIter :
    aig.latchesIter.toList.length = aig.latches.size := by
  grind

@[simp, grind =]
theorem mem_latchesIter {idx : LatchIdx} :
    idx ∈ aig.latchesIter.toList ↔ idx ∈ aig.latches := by
  grind [latches]

@[grind =]
theorem toArray_latchesIter :
    aig.latchesIter.toArray = aig.latchesIter.toList.toArray := by
  grind

@[simp, grind .]
theorem nodup_latchesIter :
    aig.latchesIter.toList.Nodup := by
  grind [List.pairwise_iff_getElem]

theorem distinct_latchesIter {idx idx' : Nat} (h : idx < aig.latchesIter.length) (h' : idx' < aig.latchesIter.length)
    (diff : idx ≠ idx') :
      aig.latchesIter.toList[idx] ≠ aig.latchesIter.toList[idx'] := by
  grind [@nodup_latchesIter aig, List.pairwise_iff_getElem]

grind_pattern distinct_latchesIter => aig.latchesIter.toList[idx], aig.latchesIter.toList[idx'] where
  idx =/= idx'

theorem Perm_latchesIter_iff {aig aig' : Aig} :
    aig'.latchesIter.toList.Perm aig.latchesIter.toList ↔
    ∀ (idx : LatchIdx), idx ∈ aig'.latches ↔ idx ∈ aig.latches := by
  constructor
  · grind [=_ mem_latchesIter, List.Perm.mem_iff]
  · grind [List.Nodup.count]

theorem size_latches_eq_of_mem_latches_eq {aig aig' : Aig} (h : ∀ (idx : LatchIdx), idx ∈ aig'.latches ↔ idx ∈ aig.latches) :
    aig'.latches.size = aig.latches.size := by
  grind [=_ length_toList_latchesIter, Perm_latchesIter_iff, List.Perm.length_eq]

@[simp]
theorem toList_latchesIter_subset_mono {old new : Aig} (mono : old ≤ new) :
    old.latchesIter.toList ⊆ new.latchesIter.toList := by
  grind

end latchesIter

end Valaig.Aig
