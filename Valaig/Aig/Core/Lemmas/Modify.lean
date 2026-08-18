module

public import Valaig.Aig.Core.Basic
import Valaig.Aig.Core.Lemmas.Basic
import all Valaig.Aig.Core.Basic
import Valaig.Aig.Core.Lemmas.Monotone

namespace Valaig.Aig
open Data (AbsMap)
variable {aig : Aig}

attribute [local grind] nodes inputs latches

/-
  `pushNode`.
-/
section pushNode
variable {node : NodeData}
attribute [local simp, local grind] pushNode NodeData.toNode newInputIdx newLatchIdx

@[simp, grind =]
theorem nodes_pushNode :
    (aig.pushNode node).nodes = aig.nodes.push aig.nextVar (node.toNode aig.nextVar) := by
  apply AbsMap.ext' <;> grind

@[simp, grind =]
theorem inputs_pushNode :
    (aig.pushNode node).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_pushNode :
    (aig.pushNode node).latches = aig.latches := by
  grind

@[simp, grind =]
theorem newInputIdx_pushNode :
    (aig.pushNode node).newInputIdx = aig.newInputIdx := by
  grind

@[simp, grind =]
theorem newLatchIdx_pushNode :
    (aig.pushNode node).newLatchIdx = aig.newLatchIdx := by
  grind

@[simp, grind! .]
theorem mono_pushNode :
    aig ≤ aig.pushNode node := by
  constructor <;> grind

end pushNode

/-
  `setNode`.
-/
section setNode
variable {var : Var} {node : NodeData} (valid : var.validIn aig)
attribute [local simp, local grind] setNode NodeData.toNode newInputIdx newLatchIdx

@[simp, grind =]
theorem nodes_setNode :
    (aig.setNode var node valid).nodes = aig.nodes.set var (node.toNode var) := by
  apply AbsMap.ext' <;> grind

@[simp, grind =]
theorem inputs_setNode :
    (aig.setNode var node valid).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_setNode :
    (aig.setNode var node valid).latches = aig.latches := by
  grind

@[simp, grind =]
theorem newInputIdx_setNode :
    (aig.setNode var node valid).newInputIdx = aig.newInputIdx := by
  grind

@[simp, grind =]
theorem newLatchIdx_setNode :
    (aig.setNode var node valid).newLatchIdx = aig.newLatchIdx := by
  grind

@[grind .]
theorem mono_setNode {other : Aig} (mono : other ≤ aig) (h : var ∉ other.nodes) :
    other ≤ aig.setNode var node valid := by
  constructor
  · constructor <;> grind
  all_goals grind

end setNode

/-
  `pushInput`.
-/
section pushInput
variable {input : Input} (h : input.var ≠ .constant)
attribute [local simp, local grind] pushInput newInputIdx

@[simp, grind =]
theorem nodes_pushInput :
    (aig.pushInput input h).nodes = aig.nodes := by
  grind

@[simp, grind =]
theorem inputs_pushInput :
    (aig.pushInput input h).inputs = aig.inputs.push aig.newInputIdx input := by
  grind

@[simp, grind =]
theorem latches_pushInput :
    (aig.pushInput input h).latches = aig.latches := by
  grind

@[simp, grind! .]
theorem mono_pushInput :
    aig ≤ aig.pushInput input h := by
  constructor <;> grind

end pushInput

/-
  `pushLatch`.
-/
section pushLatch
variable {latch : Latch} (h : latch.var ≠ .constant)
attribute [local simp, local grind] pushLatch newLatchIdx

@[simp, grind =]
theorem nodes_pushLatch :
    (aig.pushLatch latch h).nodes = aig.nodes := by
  grind

@[simp, grind =]
theorem inputs_pushLatch :
    (aig.pushLatch latch h).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_pushLatch :
    (aig.pushLatch latch h).latches = aig.latches.push aig.newLatchIdx latch := by
  grind

@[simp, grind! .]
theorem mono_pushLatch :
    aig ≤ aig.pushLatch latch h := by
  constructor <;> grind

end pushLatch

/-
  `eraseInput`.
-/
section eraseInput
variable {idx : InputIdx} (valid : idx.validIn aig)
attribute [local simp, local grind] eraseInput

@[simp, grind =]
theorem nodes_eraseInput :
    (aig.eraseInput idx valid).nodes = aig.nodes := by
  grind

@[simp, grind =]
theorem inputs_eraseInput :
    (aig.eraseInput idx valid).inputs = aig.inputs.erase idx := by
  grind

@[simp, grind =]
theorem latches_eraseInput :
    (aig.eraseInput idx valid).latches = aig.latches := by
  grind

end eraseInput

/-
  `eraseLatch`.
-/
section eraseLatch
variable {idx : LatchIdx} (valid : idx.validIn aig)
attribute [local simp, local grind] eraseLatch

@[simp, grind =]
theorem nodes_eraseLatch :
    (aig.eraseLatch idx valid).nodes = aig.nodes := by
  grind

@[simp, grind =]
theorem inputs_eraseLatch :
    (aig.eraseLatch idx valid).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_eraseLatch :
    (aig.eraseLatch idx valid).latches = aig.latches.erase idx := by
  grind

end eraseLatch

/-
  `moveInput`.
-/
section moveInput
variable {old new : InputIdx} (valid : old.validIn aig) (notvalid : ¬new.validIn aig ∨ new = old)
attribute [local simp, local grind] moveInput

@[simp, grind =]
theorem nodes_moveInput :
    (aig.moveInput old new valid notvalid).nodes = aig.nodes := by
  grind

@[simp, grind =]
theorem inputs_moveInput :
    (aig.moveInput old new valid notvalid).inputs = aig.inputs.move old new := by
  grind

@[simp, grind =]
theorem latches_moveInput :
    (aig.moveInput old new valid notvalid).latches = aig.latches := by
  grind

end moveInput

/-
  `moveLatch`.
-/
section moveLatch
variable {old new : LatchIdx} (valid : old.validIn aig) (notvalid : ¬new.validIn aig ∨ new = old)
attribute [local simp, local grind] moveLatch

@[simp, grind =]
theorem nodes_moveLatch :
    (aig.moveLatch old new valid notvalid).nodes = aig.nodes := by
  grind

@[simp, grind =]
theorem inputs_moveLatch :
    (aig.moveLatch old new valid notvalid).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_moveLatch :
    (aig.moveLatch old new valid notvalid).latches = aig.latches.move old new := by
  grind
end moveLatch

public section

/-
  `empty`.
-/
section empty
attribute [local simp, local grind] empty

@[simp, grind =]
theorem size_nodes_empty :
    empty.nodes.size = 1 := by
  grind

@[simp, grind =]
theorem mem_nodes_empty {var : Var} :
    var ∈ empty.nodes ↔ var = .constant := by
  grind

@[simp, grind =]
theorem getElem_nodes_empty {var : Var} (mem : var ∈ empty.nodes) :
    empty.nodes[var] = .false := by
  grind

@[simp, grind =]
theorem inputs_empty :
    empty.inputs = .empty := by
  grind

@[simp, grind =]
theorem latches_empty :
    empty.latches = .empty := by
  grind

@[simp, grind .]
theorem mono_empty (new : Aig) :
    empty ≤ new := by
  constructor <;> constructor <;> grind

end empty

/-
  `setNext`.
-/
section setNext
variable {idx : LatchIdx} {next : Lit} {valid : idx.validIn aig}
attribute [local simp, local grind] setNext

@[simp, grind =]
theorem nodes_setNext :
    (aig.setNext idx next valid).nodes = aig.nodes := by
  grind

@[simp, grind =]
theorem inputs_setNext :
    (aig.setNext idx next valid).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_setNext :
    (aig.setNext idx next valid).latches = aig.latches.modify idx ({ · with next }) := by
  apply AbsMap.ext' <;> grind

@[grind .]
theorem mono_setNext {other : Aig} (mono : other ≤ aig) (h : idx ∉ other.latches) :
    other ≤ aig.setNext idx next valid := by
  constructor
  · grind
  · grind
  · constructor
    · grind
    · grind [mono.latches.sized]
    · grind

end setNext

/-
  `setReset`.
-/
section setReset
variable {idx : LatchIdx} {reset : Option Lit} {valid : idx.validIn aig}
attribute [local simp, local grind] setReset

@[simp, grind =]
theorem nodes_setReset :
    (aig.setReset idx reset valid).nodes = aig.nodes := by
  grind

@[simp, grind =]
theorem inputs_setReset :
    (aig.setReset idx reset valid).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_setReset :
    (aig.setReset idx reset valid).latches = aig.latches.modify idx ({· with reset }) := by
  apply AbsMap.ext' <;> grind

@[grind .]
theorem mono_setReset {other : Aig} (mono : other ≤ aig) (h : idx ∉ other.latches) :
    other ≤ aig.setReset idx reset valid := by
  constructor
  · grind
  · grind
  · constructor
    · grind
    · grind [mono.latches.sized]
    · grind

end setReset

/-
 `addInput`.
-/
section addInput
attribute [local simp, local grind] addInput

@[simp, grind =]
theorem snd_addInput :
    aig.addInput.snd = aig.newInputIdx := by
  grind

@[simp, grind =]
theorem nodes_addInput :
    aig.addInput.fst.nodes = aig.nodes.push aig.nextVar aig.addInput.snd := by
  grind

@[simp, grind =]
theorem inputs_addInput :
    aig.addInput.fst.inputs = aig.inputs.push aig.newInputIdx { var := aig.nextVar } := by
  grind

@[simp, grind =]
theorem latches_addInput :
    aig.addInput.fst.latches = aig.latches := by
  grind

@[simp, grind! .]
theorem mono_addInput :
    aig ≤ aig.addInput.fst := by
  grind

end addInput

/-
 `addLatch`.
-/
section addLatch
variable {next : Lit} {reset : Option Lit}
attribute [local simp, local grind] addLatch

@[simp, grind =]
theorem snd_addLatch :
    (aig.addLatch next reset).snd = aig.newLatchIdx := by
  grind

@[simp, grind =]
theorem nodes_addLatch :
    (aig.addLatch next reset).fst.nodes =
    aig.nodes.push aig.nextVar (aig.addLatch next reset).snd := by
  grind

@[simp, grind =]
theorem inputs_addLatch :
    (aig.addLatch next reset).fst.inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_addLatch :
    (aig.addLatch next reset).fst.latches =
    aig.latches.push aig.newLatchIdx { var := aig.nextVar, next, reset } := by
  grind

@[simp, grind! .]
theorem mono_addLatch :
    aig ≤ (aig.addLatch next reset).fst := by
  grind

end addLatch

/-
 `addAndRaw`.
-/
section addAndRaw
variable {lhs rhs : Lit}
attribute [local simp, local grind] addAndRaw

@[simp, grind =]
theorem snd_addAndRaw :
    (aig.addAndRaw lhs rhs).snd = aig.nextVar := by
  grind

@[simp, grind =]
theorem nodes_addAndRaw (hl : lhs.validIn aig) (hr : rhs.validIn aig) :
    (aig.addAndRaw lhs rhs).fst.nodes =
    aig.nodes.push aig.nextVar (.and lhs rhs) := by
  have : lhs.var ≠ aig.nextVar ∧ rhs.var ≠ aig.nextVar := by grind
  grind

theorem nodes_addAndRaw' (hl : lhs.var ≠ aig.nextVar) (hr : rhs.var ≠ aig.nextVar) :
    (aig.addAndRaw lhs rhs).fst.nodes =
    aig.nodes.push aig.nextVar (.and lhs rhs) := by
  grind

@[simp, grind =]
theorem inputs_addAndRaw :
    (aig.addAndRaw lhs rhs).fst.inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_addAndRaw :
    (aig.addAndRaw lhs rhs).fst.latches = aig.latches := by
  grind

@[simp, grind! .]
theorem mono_addAndRaw :
    aig ≤ (aig.addAndRaw lhs rhs).fst := by
  grind

end addAndRaw

/-
 `addAnd`.
-/
section addAnd
variable {lhs rhs : Lit}
attribute [local simp, local grind] addAnd

@[grind .]
theorem size_nodes_addAnd :
    (aig.addAnd lhs rhs).fst.nodes.size = aig.nodes.size ∨
    (aig.addAnd lhs rhs).fst.nodes.size = aig.nodes.size + 1 := by
  simp [addAndRaw]

-- TODO: We need that things are WF such that l0/l1/r0/r1 are valid
@[simp, grind =]
theorem mem_nodes_addAnd {var : Var} :
    var ∈ (aig.addAnd lhs rhs).fst.nodes ↔
    var ∈ aig.nodes ∨ var = (aig.addAnd lhs rhs).snd.var := by
  simp [addAndRaw]

set_option linter.unusedVariables false in
@[simp]
theorem getElem_nodes_addAnd (hl : lhs.validIn aig) (hr : rhs.validIn aig) (new : (aig.addAnd lhs rhs).snd.var ∉ aig.nodes) :
    (aig.addAnd lhs rhs).fst[(aig.addAnd lhs rhs).snd.var] matches .and _ _ := by
  grind

grind_pattern getElem_nodes_addAnd => (aig.addAnd lhs rhs).fst[(aig.addAnd lhs rhs).snd.var]

@[simp, grind =]
theorem inputs_addAnd :
    (aig.addAnd lhs rhs).fst.inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_addAnd :
    (aig.addAnd lhs rhs).fst.latches = aig.latches := by
  grind

@[simp, grind! .]
theorem mono_addAnd :
    aig ≤ (aig.addAnd lhs rhs).fst := by
  grind

end addAnd

/-
 `inputToLatch`.
-/
section inputToLatch
variable {idx : InputIdx} {next : Lit} {reset : Option Lit}
variable (valid : idx.validIn aig) (varValid : (idx.getVar aig valid).validIn aig)
attribute [local simp, local grind] inputToLatch

@[simp, grind =]
theorem snd_inputToLatch :
    (aig.inputToLatch idx next reset valid varValid).snd = aig.newLatchIdx := by
  grind

@[simp, grind =]
theorem nodes_inputToLatch :
    (aig.inputToLatch idx next reset valid varValid).fst.nodes =
    aig.nodes.set (idx.getVar aig) (aig.inputToLatch idx next reset).snd := by
  grind

@[simp, grind =]
theorem inputs_inputToLatch :
    (aig.inputToLatch idx next reset valid varValid).fst.inputs = aig.inputs.erase idx := by
  grind

@[simp, grind =]
theorem latches_inputToLatch :
    (aig.inputToLatch idx next reset valid varValid).fst.latches =
    aig.latches.push
      (aig.inputToLatch idx next reset).snd
      { var := idx.getVar aig, next, reset } := by
  grind

end inputToLatch

/-
 `inputToAnd`.
-/
section inputToAnd
variable {idx : InputIdx} {lhs rhs : Lit}
variable (valid : idx.validIn aig) (varValid : (idx.getVar aig valid).validIn aig)
attribute [local simp, local grind] inputToAnd


@[simp, grind =]
theorem nodes_inputToAnd (hl : lhs.var ≠ idx.getVar aig) (hr : rhs.var ≠ idx.getVar aig) :
    (aig.inputToAnd idx lhs rhs valid varValid).nodes =
    aig.nodes.set (idx.getVar aig) (.and lhs rhs) := by
  grind

@[simp, grind =]
theorem inputs_inputToAnd :
    (aig.inputToAnd idx lhs rhs valid varValid).inputs = aig.inputs.erase idx := by
  grind

@[simp, grind =]
theorem latches_inputToAnd :
    (aig.inputToAnd idx lhs rhs valid varValid).latches = aig.latches := by
  grind

end inputToAnd

/-
 `changeInputIdx`.
-/
section changeInputIdx
variable {old new : InputIdx}
variable (valid : old.validIn aig) (varValid : (old.getVar aig valid).validIn aig) (unused : ¬new.validIn aig ∨ old = new)
attribute [local simp, local grind] changeInputIdx

@[simp, grind =]
theorem nodes_changeInputIdx :
    (aig.changeInputIdx old new valid varValid unused).nodes = aig.nodes.set (old.getVar aig) new := by
  grind

@[simp, grind =]
theorem size_inputs_changeInputIdx :
    (aig.changeInputIdx old new valid varValid unused).inputs.size = aig.inputs.size := by
  grind

@[simp, grind =]
theorem mem_inputs_changeInputIdx {idx : InputIdx} :
    idx ∈ (aig.changeInputIdx old new valid varValid unused).inputs ↔
    (idx ∈ aig.inputs ∧ idx ≠ old) ∨ idx = new := by
  grind

@[simp, grind =]
theorem getElem_inputs_changeInputIdx {idx : InputIdx}
    (mem : idx ∈ (aig.changeInputIdx old new valid varValid unused).inputs) :
    (aig.changeInputIdx old new valid varValid unused).inputs[idx] =
    if _ : idx = new then
      aig.inputs[old]
    else
      have h : idx ∈ aig.inputs := by grind
      aig.inputs[idx]'h := by
  grind

@[simp, grind =]
theorem latches_changeInputIdx :
    (aig.changeInputIdx old new valid varValid unused).latches = aig.latches := by
  grind

end changeInputIdx

/-
 `latchToInput`.
-/
section latchToInput
variable {idx : LatchIdx} (valid : idx.validIn aig) (varValid : (idx.getVar aig valid).validIn aig)
attribute [local simp, local grind] latchToInput

@[simp, grind =]
theorem snd_latchToInput :
    (aig.latchToInput idx valid varValid).snd = aig.newInputIdx := by
  grind

@[simp, grind =]
theorem nodes_latchToInput :
    (aig.latchToInput idx valid varValid).fst.nodes =
    aig.nodes.set (idx.getVar aig) (aig.latchToInput idx).snd := by
  grind

@[simp, grind =]
theorem inputs_latchToInput :
    (aig.latchToInput idx valid varValid).fst.inputs =
    aig.inputs.push (aig.latchToInput idx valid).snd { var := idx.getVar aig } := by
  grind

@[simp, grind =]
theorem latches_latchToInput :
    (aig.latchToInput idx valid varValid).fst.latches = aig.latches.erase idx := by
  grind

end latchToInput

/-
 `latchToAnd`.
-/
section latchToAnd
variable {idx : LatchIdx} {lhs rhs : Lit}
variable (valid : idx.validIn aig) (varValid : (idx.getVar aig valid).validIn aig)
attribute [local simp, local grind] latchToAnd


@[simp, grind =]
theorem nodes_latchToAnd (hl : lhs.var ≠ idx.getVar aig) (hr : rhs.var ≠ idx.getVar aig) :
    (aig.latchToAnd idx lhs rhs valid varValid).nodes =
    aig.nodes.set (idx.getVar aig) (.and lhs rhs) := by
  grind

@[simp, grind =]
theorem inputs_latchToAnd :
    (aig.latchToAnd idx lhs rhs valid varValid).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_latchToAnd :
    (aig.latchToAnd idx lhs rhs valid varValid).latches = aig.latches.erase idx := by
  grind

end latchToAnd

/-
 `changeLatchIdx`.
-/
section changeLatchIdx
variable {old new : LatchIdx}
variable (valid : old.validIn aig) (varValid : (old.getVar aig valid).validIn aig) (unused : ¬new.validIn aig ∨ old = new)
attribute [local simp, local grind] changeLatchIdx

@[simp, grind =]
theorem nodes_changeLatchIdx :
    (aig.changeLatchIdx old new valid varValid unused).nodes = aig.nodes.set (old.getVar aig) new := by
  grind

@[simp, grind =]
theorem inputs_changeLatchIdx :
    (aig.changeLatchIdx old new valid varValid unused).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem size_latches_changeLatchIdx :
    (aig.changeLatchIdx old new valid varValid unused).latches.size = aig.latches.size := by
  grind

@[simp, grind =]
theorem mem_latches_changeLatchIdx {idx : LatchIdx} :
    idx ∈ (aig.changeLatchIdx old new valid varValid unused).latches ↔
    (idx ∈ aig.latches ∧ idx ≠ old) ∨ idx = new := by
  grind

@[simp, grind =]
theorem getElem_latches_changeLatchIdx {idx : LatchIdx}
    (mem : idx ∈ (aig.changeLatchIdx old new valid varValid unused).latches) :
    (aig.changeLatchIdx old new valid varValid unused).latches[idx] =
    if _ : idx = new then
      aig.latches[old]
    else
      have h : idx ∈ aig.latches := by grind
      aig.latches[idx]'h := by
  grind

end changeLatchIdx

/-
  `andToInput`.
-/
section andToInput
variable {var : Var} (valid : var.validIn aig)
attribute [local simp, local grind] andToInput

@[simp, grind =]
theorem snd_andToInput isAnd :
    (aig.andToInput var valid isAnd).snd = aig.newInputIdx := by
  grind

@[simp, grind =]
theorem nodes_andToInput isAnd :
    (aig.andToInput var valid isAnd).fst.nodes =
    aig.nodes.set var (aig.andToInput var valid isAnd).snd := by
  grind

@[simp, grind =]
theorem inputs_andToInput isAnd :
    (aig.andToInput var valid isAnd).fst.inputs =
    aig.inputs.push aig.newInputIdx { var } := by
  grind

@[simp, grind =]
theorem latches_andToInput isAnd :
    (aig.andToInput var valid isAnd).fst.latches = aig.latches := by
  grind

end andToInput

/-
  `andToLatch`.
-/
section andToLatch
variable {var : Var} {next : Lit} {reset : Option Lit} (valid : var.validIn aig)
attribute [local simp, local grind] andToLatch

@[simp, grind =]
theorem snd_andToLatch isAnd :
    (aig.andToLatch var next reset valid isAnd).snd = aig.newLatchIdx := by
  grind

@[simp, grind =]
theorem nodes_andToLatch isAnd :
    (aig.andToLatch var next reset valid isAnd).fst.nodes =
    aig.nodes.set var (aig.andToLatch var next reset valid isAnd).snd := by
  grind

@[simp, grind =]
theorem inputs_andToLatch isAnd :
    (aig.andToLatch var next reset valid isAnd).fst.inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_andToLatch isAnd :
    (aig.andToLatch var next reset valid isAnd).fst.latches =
    aig.latches.push aig.newLatchIdx { var, next, reset } := by
  grind

end andToLatch

/-
  `rewriteAnd`.
-/
section rewriteAnd
variable {var : Var} {lhs rhs : Lit} (valid : var.validIn aig)
attribute [local simp, local grind] rewriteAnd

@[simp, grind =]
theorem nodes_rewriteAnd isAnd (hl : lhs.var ≠ var) (hr : rhs.var ≠ var) :
    (aig.rewriteAnd var lhs rhs valid isAnd).nodes =
    aig.nodes.set var (.and lhs rhs) := by
  simp (disch := grind)

@[simp, grind =]
theorem inputs_rewriteAnd isAnd :
    (aig.rewriteAnd var lhs rhs valid isAnd).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_rewriteAnd isAnd :
    (aig.rewriteAnd var lhs rhs valid isAnd).latches = aig.latches := by
  grind

end rewriteAnd

end
end Valaig.Aig
