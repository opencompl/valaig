module

public import Valaig.Aig.BasicNew
import all Valaig.Aig.BasicNew
public import Valaig.Aig.IdxValidity

public section pub
namespace Valaig.Aig
variable {aig : Aig}

setup_get_set_definitions

/-
We consider the following getters:
- Aig.get
- InputIdx.getVar
- LatchIdx.getVar
- LatchIdx.getNext
- LatchIdx.getReset

and the following modifiers:
- LatchIdx.setNext
- LatchIdx.setReset
- Aig.addInput
- Aig.addLatch
- Aig.addAnd

TODO: macro generate these
-/

/-
LatchIdx.setNext Lemmas.
-/
section setNext
variable {setIdx : LatchIdx} {setValid : setIdx.validIn aig} {newNext : Lit}

@[simp, grind =]
theorem get_LatchIdx_setNext {var : Var} {valid : var.validIn aig} :
    (setIdx.setNext aig newNext setValid).get var = aig.get var valid := by
  simp

@[simp, grind =]
theorem InputIdx.getVar_LatchIdx_setNext {idx : InputIdx} {valid : idx.validIn aig} :
    idx.getVar (setIdx.setNext aig newNext setValid) = idx.getVar aig := by
  simp

@[simp, grind =]
theorem LatchIdx.getVar_LatchIdx_setNext {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getVar (setIdx.setNext aig newNext setValid) = idx.getVar aig := by
  simp; grind

@[simp, grind =]
theorem LatchIdx.getNext_LatchIdx_setNext_self {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getNext (setIdx.setNext aig newNext setValid) =
    if idx = setIdx then newNext else idx.getNext aig := by
  simp; grind

@[simp, grind =]
theorem LatchIdx.getReset_LatchIdx_setNext {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getReset (setIdx.setNext aig newNext setValid) = idx.getReset aig := by
  simp; grind

end setNext

/-
LatchIdx.setReset Lemmas.
-/
section setReset
variable {setIdx : LatchIdx} {setValid : setIdx.validIn aig} {newReset : Lit}

@[simp, grind =]
theorem get_LatchIdx_setReset {var : Var} {valid : var.validIn aig} :
    (setIdx.setReset aig newReset setValid).get var = aig.get var valid := by
  simp

@[simp, grind =]
theorem InputIdx.getVar_LatchIdx_setReset {idx : InputIdx} {valid : idx.validIn aig} :
    idx.getVar (setIdx.setReset aig newReset setValid) = idx.getVar aig := by
  simp

@[simp, grind =]
theorem LatchIdx.getVar_LatchIdx_setReset {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getVar (setIdx.setReset aig newReset setValid) = idx.getVar aig := by
  simp; grind

@[simp, grind =]
theorem LatchIdx.getNext_LatchIdx_setReset {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getNext (setIdx.setReset aig newReset setValid) = idx.getNext aig := by
  simp; grind

@[simp, grind =]
theorem LatchIdx.getReset_LatchIdx_setReset {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getReset (setIdx.setReset aig newReset setValid) =
    if idx = setIdx then newReset else idx.getReset aig := by
  simp; grind

end setReset

section aig

-- These are needed for grind to reason about index validity
attribute [local simp, local grind] Var.validIn InputIdx.validIn LatchIdx.validIn

/-
Aig.addInput Lemmas.
-/
section addInput

@[simp, grind =]
theorem get_Aig_addInput {var : Var} {valid : var.validIn aig} :
    aig.addInput.fst.get var = aig.get var valid := by
  simp; grind

@[simp, grind =]
theorem InputIdx.getVar_Aig_addInput {idx : InputIdx} {valid : idx.validIn aig} :
    idx.getVar aig.addInput.fst = idx.getVar aig valid := by
  simp; grind

@[simp, grind =]
theorem LatchIdx.getVar_Aig_addInput {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getVar aig.addInput.fst = idx.getVar aig valid := by
  simp

@[simp, grind =]
theorem LatchIdx.getNext_Aig_addInput {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getNext aig.addInput.fst = idx.getNext aig valid := by
  simp

@[simp, grind =]
theorem LatchIdx.getReset_Aig_addInput {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getReset aig.addInput.fst = idx.getReset aig valid := by
  simp

end addInput

/-
Aig.addLatch Lemmas.
-/
section addLatch
variable {next reset : Lit}

@[simp, grind =]
theorem get_Aig_addLatch {var : Var} {valid : var.validIn aig} :
    (aig.addLatch next reset).fst.get var = aig.get var valid := by
  simp; grind

@[simp, grind =]
theorem InputIdx.getVar_Aig_addLatch {idx : InputIdx} {valid : idx.validIn aig} :
    idx.getVar (aig.addLatch next reset).fst = idx.getVar aig valid := by
  simp

@[simp, grind =]
theorem LatchIdx.getVar_Aig_addLatch {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getVar (aig.addLatch next reset).fst = idx.getVar aig valid := by
  simp; grind

@[simp, grind =]
theorem LatchIdx.getNext_Aig_addLatch {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getNext (aig.addLatch next reset).fst = idx.getNext aig valid := by
  simp; grind

@[simp, grind =]
theorem LatchIdx.getNext_Aig_addLatch_eq_self :
  (aig.addLatch next reset).snd.getNext (aig.addLatch next reset).fst = next := by
  simp

@[simp, grind =]
theorem LatchIdx.getReset_Aig_addLatch {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getReset (aig.addLatch next reset).fst = idx.getReset aig valid := by
  simp; grind

@[simp, grind =]
theorem LatchIdx.getReset_Aig_addLatch_eq_self :
  (aig.addLatch next reset).snd.getReset (aig.addLatch next reset).fst = reset := by
  simp

end addLatch

/-
Aig.addAnd Lemmas.
-/
section addAnd
variable {rhs0 rhs1 : Lit} {h0 : rhs0.validIn aig} {h1 : rhs1.validIn aig}

@[simp, grind =]
theorem get_Aig_addAnd {var : Var} {valid : var.validIn aig} :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.get var = aig.get var valid := by
  simp; grind

@[simp, grind =]
theorem InputIdx.getVar_Aig_addAnd {idx : InputIdx} {valid : idx.validIn aig} :
    idx.getVar (aig.addAnd rhs0 rhs1 h0 h1).fst = idx.getVar aig valid := by
  simp

@[simp, grind =]
theorem LatchIdx.getVar_Aig_addAnd {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getVar (aig.addAnd rhs0 rhs1 h0 h1).fst = idx.getVar aig valid := by
  simp

@[simp, grind =]
theorem LatchId.getNext_Aig_addAnd {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getNext (aig.addAnd rhs0 rhs1 h0 h1).fst = idx.getNext aig valid := by
  simp

@[simp, grind =]
theorem LatchIdx.getReset_Aig_addAnd {idx : LatchIdx} {valid : idx.validIn aig} :
    idx.getReset (aig.addAnd rhs0 rhs1 h0 h1).fst = idx.getReset aig valid := by
  simp

end addAnd

end aig
