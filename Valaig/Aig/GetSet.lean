module

import Valaig.Prelude
import all Valaig.Aig.Basic
public import Valaig.Aig.ValidIn

public section
namespace Valaig.Aig
variable {aig : Aig}

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

We include the (by grind) arguments throughout because lean's elaboration seems
to be significantly slower otherwise (for unclear reasons).

TODO: only use get/sets for the bodies of theorems, and use existing validity
theorems for proving arguments valid.
-/

local macro "simp_grind" : tactic => `(tactic| ((try simp_defs) <;> grind_defs))

@[simp, grind =]
theorem get_constant :
    aig.get .constant = .false := by
  have := aig.aig.hconst
  simp_all_defs

/-
Aig.empty Lemmas. There aren't many as the only valid ref/index is the constant
variable.
-/
section empty

@[simp, grind =]
theorem get_empty {var : Var} (valid : var.validIn empty) :
    empty.get var = .false := by
  grind

end empty

/-
LatchIdx.setNext Lemmas.
-/
section setNext
variable {setIdx : LatchIdx} {setValid : setIdx.validIn aig} {newNext : Lit}

@[simp, grind =]
theorem get_setNext {var : Var} (valid : var.validIn aig) :
    (setIdx.setNext aig newNext setValid).get var (by grind) = aig.get var valid := by
  simp_grind

@[simp, grind =]
theorem input_getVar_setNext {idx : InputIdx} (valid : idx.validIn aig) :
    idx.getVar (setIdx.setNext aig newNext setValid) (by grind) = idx.getVar aig valid := by
  simp_grind

@[simp, grind =]
theorem latch_getVar_setNext {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getVar (setIdx.setNext aig newNext setValid) (by grind) = idx.getVar aig valid := by
  simp_grind

@[simp, grind =]
theorem getNext_setNext_self {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getNext (setIdx.setNext aig newNext setValid) (by grind) =
    if idx = setIdx then newNext else idx.getNext aig valid := by
  simp_grind

@[simp, grind =]
theorem getReset_setNext {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getReset (setIdx.setNext aig newNext setValid) (by grind) = idx.getReset aig valid := by
  simp_grind

end setNext

/-
LatchIdx.setReset Lemmas.
-/
section setReset
variable {setIdx : LatchIdx} {setValid : setIdx.validIn aig} {newReset : Lit}

@[simp, grind =]
theorem get_setReset {var : Var} {valid : var.validIn aig} :
    (setIdx.setReset aig newReset setValid).get var (by grind) = aig.get var valid := by
  simp_grind

@[simp, grind =]
theorem input_getVar_setReset {idx : InputIdx} (valid : idx.validIn aig) :
    idx.getVar (setIdx.setReset aig newReset setValid) (by grind) = idx.getVar aig valid := by
  simp_grind

@[simp, grind =]
theorem latch_getVar_setReset {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getVar (setIdx.setReset aig newReset setValid) (by grind) = idx.getVar aig valid := by
  simp_grind

@[simp, grind =]
theorem getNext_setReset {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getNext (setIdx.setReset aig newReset setValid) (by grind) = idx.getNext aig valid := by
  simp_grind

@[simp, grind =]
theorem getReset_setReset {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getReset (setIdx.setReset aig newReset setValid) (by grind) =
    if idx = setIdx then newReset else idx.getReset aig valid := by
  simp_grind

end setReset

section aig

-- These are needed for grind to reason about index validity
attribute [local simp, local grind] Var.validIn InputIdx.validIn LatchIdx.validIn
attribute [local simp, local grind] Aig.numInputs Aig.numLatches

/-
Aig.addInput Lemmas.
-/
section addInput

@[simp, grind =]
theorem get_addInput {var : Var} {valid : var.validIn aig} :
    aig.addInput.fst.get var (by grind) = aig.get var valid := by
  simp_grind

@[simp, grind =]
theorem get_addInput_self :
    aig.addInput.fst.get (aig.addInput.snd.getVar aig.addInput.fst) (by grind) =
    .input aig.addInput.snd := by
  simp_grind

@[simp, grind =]
theorem input_getVar_addInput {idx : InputIdx} (valid : idx.validIn aig) :
    idx.getVar aig.addInput.fst (by grind) = idx.getVar aig valid := by
  simp_grind

@[simp, grind =]
theorem latch_getVar_addInput {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getVar aig.addInput.fst (by grind) = idx.getVar aig valid := by
  simp_grind

@[simp, grind =]
theorem getNext_addInput {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getNext aig.addInput.fst (by grind) = idx.getNext aig valid := by
  simp_grind

@[simp, grind =]
theorem getReset_addInput {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getReset aig.addInput.fst (by grind) = idx.getReset aig valid := by
  simp_grind

end addInput

/-
Aig.addLatch Lemmas.
-/
section addLatch
variable {next reset : Lit}

@[simp, grind =]
theorem get_addLatch {var : Var} (valid : var.validIn aig) :
    (aig.addLatch next reset).fst.get var (by grind) = aig.get var valid := by
  simp_grind

@[simp, grind =]
theorem get_addLatch_self :
    (aig.addLatch next reset).fst.get
      ((aig.addLatch next reset).snd.getVar (aig.addLatch next reset).fst)
      (by grind) =
    .latch (aig.addLatch next reset).snd := by
  simp_grind

@[simp, grind =]
theorem input_getVar_addLatch {idx : InputIdx} (valid : idx.validIn aig) :
    idx.getVar (aig.addLatch next reset).fst (by grind) = idx.getVar aig valid := by
  simp_grind

@[simp, grind =]
theorem latch_getVar_addLatch {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getVar (aig.addLatch next reset).fst (by grind) = idx.getVar aig valid := by
  simp_grind

@[simp, grind =]
theorem getNext_addLatch {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getNext (aig.addLatch next reset).fst (by grind) = idx.getNext aig valid := by
  simp_grind

@[simp, grind =]
theorem getNext_addLatch_self :
  (aig.addLatch next reset).snd.getNext (aig.addLatch next reset).fst (by grind) = next := by
  simp_grind

@[simp, grind =]
theorem getReset_addLatch {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getReset (aig.addLatch next reset).fst (by grind) = idx.getReset aig valid := by
  simp_grind

@[simp, grind =]
theorem getReset_addLatch_self :
  (aig.addLatch next reset).snd.getReset (aig.addLatch next reset).fst (by grind) = reset := by
  simp_grind

end addLatch

/-
Aig.addAnd Lemmas.
-/
section addAnd
variable {rhs0 rhs1 : Lit} {h0 : rhs0.validIn aig} {h1 : rhs1.validIn aig}

@[simp, grind =]
theorem get_addAnd {var : Var} (valid : var.validIn aig) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.get var (by grind) = aig.get var valid := by
  simp_grind

@[simp]
theorem get_addAnd_new_matches_and {var : Var}
    (notValid : ¬var.validIn aig)
    (valid : var.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst) :
    ∃ (lhs rhs : Lit), (aig.addAnd rhs0 rhs1 h0 h1).fst.get var = .and lhs rhs := by
  simp_all_defs
  split <;> grind [Std.mkAndCached_matches_gate]

@[simp, grind =]
theorem input_getVar_addAnd {idx : InputIdx} (valid : idx.validIn aig) :
    idx.getVar (aig.addAnd rhs0 rhs1 h0 h1).fst (by grind) = idx.getVar aig valid := by
  simp_grind

@[simp, grind =]
theorem latch_getVar_addAnd {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getVar (aig.addAnd rhs0 rhs1 h0 h1).fst (by grind) = idx.getVar aig valid := by
  simp_grind

@[simp, grind =]
theorem getNext_addAnd {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getNext (aig.addAnd rhs0 rhs1 h0 h1).fst (by grind) = idx.getNext aig valid := by
  simp_grind

@[simp, grind =]
theorem getReset_addAnd {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getReset (aig.addAnd rhs0 rhs1 h0 h1).fst (by grind) = idx.getReset aig valid := by
  simp_grind

end addAnd

end aig
