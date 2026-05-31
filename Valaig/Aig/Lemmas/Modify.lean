module

import all Valaig.Aig.Basic
public import Valaig.Aig.Lemmas.Basic
import Valaig.Aig.Lemmas.Monotone

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
theorem latchs_pushLatch :
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
  `LatchIdx.setNext`.
-/
section latch_setNext
variable {idx : LatchIdx} {next : Lit} {valid : idx.validIn aig}
attribute [local simp, local grind] LatchIdx.setNext

@[simp, grind =]
theorem nodes_setNext :
    (idx.setNext aig next valid).nodes = aig.nodes := by
  grind

@[simp, grind =]
theorem inputs_setNext :
    (idx.setNext aig next valid).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_setNext :
    (idx.setNext aig next valid).latches = aig.latches.modify idx ({ · with next }) := by
  apply AbsMap.ext' <;> grind

end latch_setNext

/-
  `LatchIdx.setReset`.
-/
section latch_setReset
variable {idx : LatchIdx} {reset : Option Lit} {valid : idx.validIn aig}
attribute [local simp, local grind] LatchIdx.setReset

@[simp, grind =]
theorem nodes_setReset :
    (idx.setReset aig reset valid).nodes = aig.nodes := by
  grind

@[simp, grind =]
theorem inputs_setReset :
    (idx.setReset aig reset valid).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_setReset :
    (idx.setReset aig reset valid).latches = aig.latches.modify idx ({· with reset }) := by
  apply AbsMap.ext' <;> grind

end latch_setReset

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
 `addAnd`.
-/
section addAnd
variable {rhs0 rhs1 : Lit}
attribute [local simp, local grind] addAnd

@[simp, grind =]
theorem snd_addAnd :
    (aig.addAnd rhs0 rhs1).snd = aig.nextVar := by
  grind

@[simp, grind =]
theorem nodes_addAnd (h0 : rhs0.validIn aig) (h1 : rhs1.validIn aig) :
    (aig.addAnd rhs0 rhs1).fst.nodes =
    aig.nodes.push aig.nextVar (.and rhs0 rhs1) := by
  have : rhs0.var ≠ aig.nextVar ∧ rhs1.var ≠ aig.nextVar := by grind
  grind

theorem nodes_addAnd' (h0 : rhs0.var ≠ aig.nextVar) (h1 : rhs1.var ≠ aig.nextVar) :
    (aig.addAnd rhs0 rhs1).fst.nodes =
    aig.nodes.push aig.nextVar (.and rhs0 rhs1) := by
  grind

@[simp, grind =]
theorem inputs_addAnd :
    (aig.addAnd rhs0 rhs1).fst.inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_addAnd :
    (aig.addAnd rhs0 rhs1).fst.latches = aig.latches := by
  grind

@[simp, grind! .]
theorem mono_addAnd :
    aig ≤ (aig.addAnd rhs0 rhs1).fst := by
  grind

end addAnd

/-
 `InputIdx.convertToLatch`.
-/
section input_convertToLatch
variable {idx : InputIdx} {next : Lit} {reset : Option Lit}
variable (valid : idx.validIn aig) (varValid : (idx.getVar aig).validIn aig)
attribute [local simp, local grind] InputIdx.convertToLatch

@[simp, grind =]
theorem snd_input_convertToLatch :
    (idx.convertToLatch aig next reset valid varValid).snd = aig.newLatchIdx := by
  grind

@[simp, grind =]
theorem nodes_input_convertToLatch :
    (idx.convertToLatch aig next reset valid varValid).fst.nodes =
    aig.nodes.set (idx.getVar aig) (idx.convertToLatch aig next reset).snd := by
  grind

@[simp, grind =]
theorem inputs_input_convertToLatch :
    (idx.convertToLatch aig next reset valid varValid).fst.inputs = aig.inputs.erase idx := by
  grind

@[simp, grind =]
theorem latches_input_convertToLatch :
    (idx.convertToLatch aig next reset valid varValid).fst.latches =
    aig.latches.push
      (idx.convertToLatch aig next reset).snd
      { var := idx.getVar aig, next, reset } := by
  grind

end input_convertToLatch

/-
 `InputIdx.convertToAnd`.
-/
section input_convertToAnd
variable {idx : InputIdx} {rhs0 rhs1 : Lit}
variable (valid : idx.validIn aig) (varValid : (idx.getVar aig).validIn aig)
attribute [local simp, local grind] InputIdx.convertToAnd


@[simp, grind =]
theorem nodes_input_convertToAnd (h0 : rhs0.var ≠ idx.getVar aig) (h1 : rhs1.var ≠ idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).nodes =
    aig.nodes.set (idx.getVar aig) (.and rhs0 rhs1) := by
  grind

@[simp, grind =]
theorem inputs_input_convertToAnd :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).inputs = aig.inputs.erase idx := by
  grind

@[simp, grind =]
theorem latches_input_convertToAnd :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).latches = aig.latches := by
  grind

end input_convertToAnd

/-
 `InputIdx.changeIdx`.
-/
section input_changeIdx
variable {old new : InputIdx}
variable (valid : old.validIn aig) (varValid : (old.getVar aig).validIn aig) (unused : ¬new.validIn aig ∨ old = new)
attribute [local simp, local grind] InputIdx.changeIdx

@[simp, grind =]
theorem nodes_input_changeIdx :
    (old.changeIdx new aig valid varValid unused).nodes = aig.nodes.set (old.getVar aig) new := by
  grind

@[simp, grind =]
theorem size_inputs_input_changeIdx :
    (old.changeIdx new aig valid varValid unused).inputs.size = aig.inputs.size := by
  grind

@[simp, grind =]
theorem mem_inputs_input_changeIdx {idx : InputIdx} :
    idx ∈ (old.changeIdx new aig valid varValid unused).inputs ↔
    (idx ∈ aig.inputs ∧ idx ≠ old) ∨ idx = new := by
  grind

@[simp, grind =]
theorem getElem_inputs_input_changeIdx {idx : InputIdx}
    (mem : idx ∈ (old.changeIdx new aig valid varValid unused).inputs) :
    (old.changeIdx new aig valid varValid unused).inputs[idx] =
    if _ : idx = new then
      aig.inputs[old]
    else
      have h : idx ∈ aig.inputs := by grind
      aig.inputs[idx]'h := by
  grind

@[simp, grind =]
theorem latches_input_changeIdx :
    (old.changeIdx new aig valid varValid unused).latches = aig.latches := by
  grind

end input_changeIdx

/-
 `LatchIdx.convertToInput`.
-/
section latch_convertToInput
variable {idx : LatchIdx} (valid : idx.validIn aig) (varValid : (idx.getVar aig).validIn aig)
attribute [local simp, local grind] LatchIdx.convertToInput

@[simp, grind =]
theorem snd_latch_convertToInput :
    (idx.convertToInput aig valid varValid).snd = aig.newInputIdx := by
  grind

@[simp, grind =]
theorem nodes_latch_convertToInput :
    (idx.convertToInput aig valid varValid).fst.nodes =
    aig.nodes.set (idx.getVar aig) (idx.convertToInput aig).snd := by
  grind

@[simp, grind =]
theorem inputs_latch_convertToInput :
    (idx.convertToInput aig valid varValid).fst.inputs =
    aig.inputs.push (idx.convertToInput aig valid).snd { var := idx.getVar aig } := by
  grind

@[simp, grind =]
theorem latches_latch_convertToInput :
    (idx.convertToInput aig valid varValid).fst.latches = aig.latches.erase idx := by
  grind

end latch_convertToInput

/-
 `LatchIdx.convertToAnd`.
-/
section latch_convertToAnd
variable {idx : LatchIdx} {rhs0 rhs1 : Lit}
variable (valid : idx.validIn aig) (varValid : (idx.getVar aig).validIn aig)
attribute [local simp, local grind] LatchIdx.convertToAnd


@[simp, grind =]
theorem nodes_latch_convertToAnd (h0 : rhs0.var ≠ idx.getVar aig) (h1 : rhs1.var ≠ idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).nodes =
    aig.nodes.set (idx.getVar aig) (.and rhs0 rhs1) := by
  grind

@[simp, grind =]
theorem inputs_latch_convertToAnd :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_latch_convertToAnd :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).latches = aig.latches.erase idx := by
  grind

end latch_convertToAnd

/-
 `LatchIdx.changeIdx`.
-/
section latch_changeIdx
variable {old new : LatchIdx}
variable (valid : old.validIn aig) (varValid : (old.getVar aig).validIn aig) (unused : ¬new.validIn aig ∨ old = new)
attribute [local simp, local grind] LatchIdx.changeIdx

@[simp, grind =]
theorem nodes_latch_changeIdx :
    (old.changeIdx new aig valid varValid unused).nodes = aig.nodes.set (old.getVar aig) new := by
  grind

@[simp, grind =]
theorem inputs_latch_changeIdx :
    (old.changeIdx new aig valid varValid unused).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem size_latches_latch_changeIdx :
    (old.changeIdx new aig valid varValid unused).latches.size = aig.latches.size := by
  grind

@[simp, grind =]
theorem mem_latches_latch_changeIdx {idx : LatchIdx} :
    idx ∈ (old.changeIdx new aig valid varValid unused).latches ↔
    (idx ∈ aig.latches ∧ idx ≠ old) ∨ idx = new := by
  grind

@[simp, grind =]
theorem getElem_latches_latch_changeIdx {idx : LatchIdx}
    (mem : idx ∈ (old.changeIdx new aig valid varValid unused).latches) :
    (old.changeIdx new aig valid varValid unused).latches[idx] =
    if _ : idx = new then
      aig.latches[old]
    else
      have h : idx ∈ aig.latches := by grind
      aig.latches[idx]'h := by
  grind

end latch_changeIdx

/-
  `convertAndToInput`.
-/
section convertAndToInput
variable {var : Var} (valid : var.validIn aig)
attribute [local simp, local grind] convertAndToInput

@[simp, grind =]
theorem snd_convertAndToInput isAnd :
    (aig.convertAndToInput var valid isAnd).snd = aig.newInputIdx := by
  grind

@[simp, grind =]
theorem nodes_convertAndToInput isAnd :
    (aig.convertAndToInput var valid isAnd).fst.nodes =
    aig.nodes.set var (aig.convertAndToInput var valid isAnd).snd := by
  grind

@[simp, grind =]
theorem inputs_convertAndToInput isAnd :
    (aig.convertAndToInput var valid isAnd).fst.inputs =
    aig.inputs.push aig.newInputIdx { var } := by
  grind

@[simp, grind =]
theorem latches_convertAndToInput isAnd :
    (aig.convertAndToInput var valid isAnd).fst.latches = aig.latches := by
  grind

end convertAndToInput

/-
  `convertAndToLatch`.
-/
section convertAndToLatch
variable {var : Var} {next : Lit} {reset : Option Lit} (valid : var.validIn aig)
attribute [local simp, local grind] convertAndToLatch

@[simp, grind =]
theorem snd_convertAndToLatch isAnd :
    (aig.convertAndToLatch var next reset valid isAnd).snd = aig.newLatchIdx := by
  grind

@[simp, grind =]
theorem nodes_convertAndToLatch isAnd :
    (aig.convertAndToLatch var next reset valid isAnd).fst.nodes =
    aig.nodes.set var (aig.convertAndToLatch var next reset valid isAnd).snd := by
  grind

@[simp, grind =]
theorem inputs_convertAndToLatch isAnd :
    (aig.convertAndToLatch var next reset valid isAnd).fst.inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_convertAndToLatch isAnd :
    (aig.convertAndToLatch var next reset valid isAnd).fst.latches =
    aig.latches.push aig.newLatchIdx { var, next, reset } := by
  grind

end convertAndToLatch

/-
  `rewriteAnd`.
-/
section rewriteAnd
variable {var : Var} {rhs0 rhs1 : Lit} (valid : var.validIn aig)
attribute [local simp, local grind] rewriteAnd

@[simp, grind =]
theorem nodes_rewriteAnd isAnd (h0 : rhs0.var ≠ var) (h1 : rhs1.var ≠ var) :
    (aig.rewriteAnd var rhs0 rhs1 valid isAnd).nodes =
    aig.nodes.set var (.and rhs0 rhs1) := by
  simp (disch := grind)

@[simp, grind =]
theorem inputs_rewriteAnd isAnd :
    (aig.rewriteAnd var rhs0 rhs1 valid isAnd).inputs = aig.inputs := by
  grind

@[simp, grind =]
theorem latches_rewriteAnd isAnd :
    (aig.rewriteAnd var rhs0 rhs1 valid isAnd).latches = aig.latches := by
  grind

end rewriteAnd

end
end Valaig.Aig
