module

public import Valaig.Aig.Core
import Valaig.Data.DetIter

public section
namespace Valaig.Aig
variable {aig : Aig}

def checkInputs (aig : Aig) : Bool :=
  Data.DetIter.wrap aig.inputsIter
    |>.attachWith (·.validIn aig) (by grind)
    |>.all fun idx =>
      -- InputsValid
      ∃ h, aig[idx.val.getVar aig]'h = idx.val

@[grind .]
theorem InputsValid_checkInputs :
    aig.checkInputs = true ↔ aig.InputsValid := by
  rw [checkInputs, ←Std.Iter.all_toList, List.all_eq, Std.Iter.toList_attachWith, InputsValid]
  simp only [decide_eq_true_eq, Subtype.forall]
  grind

def checkLatches (aig : Aig) : Bool :=
  Data.DetIter.wrap aig.latchesIter
    |>.attachWith (·.validIn aig) (by grind)
    |>.all fun idx =>
      let var := idx.val.getVar aig
      let next := idx.val.getNext aig
      let reset := idx.val.getReset aig
      -- LatchIdxsValid
      (∃ h, aig[idx.val.getVar aig]'h = idx.val) &&
      -- NextsValid
      next.validIn aig &&
      -- ResetsValid
      reset.all (·.validIn aig) &&
      -- ResetsAcyclic
      reset.all (·.var < var)

@[local grind →]
theorem LatchesValid_checkLatches :
    aig.checkLatches = true → aig.LatchesValid := by
  rw [checkLatches, ←Std.Iter.all_toList, List.all_eq, Std.Iter.toList_attachWith, LatchesValid]
  simp only [decide_eq_true_eq, Subtype.forall]
  grind

@[local grind →]
theorem ResetsValid_checkLatches :
    aig.checkLatches = true → aig.ResetsValid := by
  rw [checkLatches, ←Std.Iter.all_toList, List.all_eq, Std.Iter.toList_attachWith, ResetsValid]
  simp only [decide_eq_true_eq, Subtype.forall]
  grind

@[local grind →]
theorem NextsValid_checkLatches :
    aig.checkLatches = true → aig.NextsValid := by
  rw [checkLatches, ←Std.Iter.all_toList, List.all_eq, Std.Iter.toList_attachWith, NextsValid]
  simp only [decide_eq_true_eq, Subtype.forall]
  grind

@[local grind →]
theorem AcyclicResets_checkLatches :
    aig.checkLatches = true → aig.AcyclicResets := by
  rw [checkLatches, ←Std.Iter.all_toList, List.all_eq, Std.Iter.toList_attachWith, AcyclicResets]
  simp only [decide_eq_true_eq, Subtype.forall]
  grind

@[simp, grind .]
theorem checkLatches_eq_true_iff :
    aig.checkLatches = true ↔
      (aig.LatchesValid ∧
      aig.ResetsValid ∧
      aig.NextsValid ∧
      aig.AcyclicResets) := by
  constructor
  · grind
  · rw [checkLatches, ←Std.Iter.all_toList, List.all_eq, Std.Iter.toList_attachWith,
      LatchesValid, ResetsValid, NextsValid, AcyclicResets]
    simp only [decide_eq_true_eq, Subtype.forall]
    grind

def checkNodes (aig : Aig) : Bool :=
  Data.DetIter.wrap aig.iter
    |>.attachWith (·.validIn aig) (by grind)
    |>.all fun var =>
      match aig[var.val] with
      | .false => true
      | .input idx
      | .latch idx =>
        -- InputsIdxsValid/LatchIdxsValid
        ∃ h, idx.getVar aig h = var
      | .and lhs rhs =>
        -- AcyclicGates
        lhs.var < var.val && rhs.var < var.val

@[local grind →]
theorem InputIdxsValid_checkNodes :
    aig.checkNodes = true → aig.InputIdxsValid := by
  rw [checkNodes, ←Std.Iter.all_toList, List.all_eq, Std.Iter.toList_attachWith, InputIdxsValid]
  simp only [decide_eq_true_eq, Subtype.forall]
  grind

@[local grind →]
theorem LatchIdxsValid_checkNodes :
    aig.checkNodes = true → aig.LatchIdxsValid := by
  rw [checkNodes, ←Std.Iter.all_toList, List.all_eq, Std.Iter.toList_attachWith, LatchIdxsValid]
  simp only [decide_eq_true_eq, Subtype.forall]
  grind

@[local grind →]
theorem AcyclicGates_checkNodes :
    aig.checkNodes = true → aig.AcyclicGates := by
  rw [checkNodes, ←Std.Iter.all_toList, List.all_eq, Std.Iter.toList_attachWith, AcyclicGates]
  simp only [decide_eq_true_eq, Subtype.forall]
  grind

@[simp, grind .]
theorem checkNodes_eq_true_iff :
    aig.checkNodes = true ↔
      aig.InputIdxsValid ∧
      aig.LatchIdxsValid ∧
      aig.AcyclicGates := by
  constructor
  · grind
  · rw [checkNodes, ←Std.Iter.all_toList, List.all_eq, Std.Iter.toList_attachWith,
      InputIdxsValid, LatchIdxsValid, AcyclicGates]
    simp only [decide_eq_true_eq, Subtype.forall]
    grind

def checkWF (aig : Aig) : Bool :=
  aig.checkInputs ∧ aig.checkLatches ∧ aig.checkNodes

@[simp, grind .]
theorem WF_checkWF :
    aig.checkWF = true ↔ aig.WF := by
  grind [WF, checkWF]

instance : Decidable aig.WF :=
  decidable_of_iff _ WF_checkWF

end Valaig.Aig
