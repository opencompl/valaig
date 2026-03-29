module

import Valaig.Prelude
import all Valaig.Aig.Basic
public import Valaig.Aig.ValidIn

public section
namespace Valaig.Aig
variable {aig : Aig}

/-
We consider the following getters:
- Aig.size
- Aig.numInputs
- Aig.numLatches
- Aig.get
- InputIdx.getVar
- LatchIdx.getVar
- LatchIdx.getNext
- LatchIdx.getReset

and the following modifiers:
- LatchIdx.setNext
- LatchIdx.setReset
- Aig.addInput'
- Aig.addInput
- Aig.addLatch'
- Aig.addLatch
- Aig.addAnd

TODO: macro generate these
-/

local macro "simp_grind" : tactic => `(tactic| ((try simp_defs) <;> grind_defs))
attribute [local simp] numInputs numLatches

@[simp, grind =]
theorem get_constant :
    aig.get .constant = .false := by
  have := aig.aig.hconst
  simp_all_defs

@[simp, grind =]
theorem get_eq_false_iff_isConstant {var : Var} (valid : var.validIn aig) :
    aig.get var = .false ↔ var = .constant := by
  have := aig.hconst
  simp_all [getElem_decls_eq_get, Var.constant_iff_idx_zero]
  grind [Var, Var.lt_decls_size_of_validIn]

/-
Aig.empty Lemmas. There aren't many as the only valid ref/index is the constant
variable.
-/
section empty

@[simp, grind =]
theorem numLatches_empty :
    empty.numLatches = 0 := by
  simp_grind

@[simp, grind =]
theorem numInputs_empty :
    empty.numInputs = 0 := by
  simp_grind

@[simp, grind =]
theorem get_empty {var : Var} (valid : var.validIn empty) :
    empty.get var = .false := by
  grind

end empty

/-
LatchIdx.setNext Lemmas.
-/
section setNext
variable {setIdx : LatchIdx} {newNext : Lit}

@[simp, grind =]
theorem size_setNext :
    (setIdx.setNext aig newNext).size = aig.size := by
  simp_grind

@[simp, grind =]
theorem numInputs_setNext :
    (setIdx.setNext aig newNext).numInputs = aig.numInputs := by
  simp_grind

@[simp, grind =]
theorem numLatches_setNext :
    (setIdx.setNext aig newNext).numLatches = aig.numLatches := by
  simp_grind

@[simp, grind =]
theorem get_setNext {var : Var} (valid : var.validIn aig) :
    (setIdx.setNext aig newNext).get var = aig.get var valid := by
  simp_grind

@[simp, grind =]
theorem input_getVar_setNext {idx : InputIdx} (valid : idx.validIn aig) :
    idx.getVar (setIdx.setNext aig newNext) = idx.getVar aig valid := by
  simp_grind

@[simp, grind =]
theorem latch_getVar_setNext {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getVar (setIdx.setNext aig newNext) = idx.getVar aig valid := by
  simp_grind

@[simp, grind =]
theorem getNext_setNext_self {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getNext (setIdx.setNext aig newNext) =
    if idx = setIdx then newNext else idx.getNext aig valid := by
  simp_grind

@[simp, grind =]
theorem getReset_setNext {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getReset (setIdx.setNext aig newNext) = idx.getReset aig valid := by
  simp_grind

end setNext

/-
LatchIdx.setReset Lemmas.
-/
section setReset
variable {setIdx : LatchIdx} {newReset : Option Lit}

@[simp, grind =]
theorem size_setReset :
    (setIdx.setReset aig newReset).size = aig.size := by
  simp_grind

@[simp, grind =]
theorem numInputs_setReset :
    (setIdx.setReset aig newReset).numInputs = aig.numInputs := by
  simp_grind

@[simp, grind =]
theorem numLatches_setReset :
    (setIdx.setReset aig newReset).numLatches = aig.numLatches := by
  simp_grind

@[simp, grind =]
theorem get_setReset {var : Var} {valid : var.validIn aig} :
    (setIdx.setReset aig newReset).get var = aig.get var valid := by
  simp_grind

@[simp, grind =]
theorem input_getVar_setReset {idx : InputIdx} (valid : idx.validIn aig) :
    idx.getVar (setIdx.setReset aig newReset) = idx.getVar aig valid := by
  simp_grind

@[simp, grind =]
theorem latch_getVar_setReset {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getVar (setIdx.setReset aig newReset) = idx.getVar aig valid := by
  simp_grind

@[simp, grind =]
theorem getNext_setReset {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getNext (setIdx.setReset aig newReset) = idx.getNext aig valid := by
  simp_grind

@[simp, grind =]
theorem getReset_setReset {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getReset (setIdx.setReset aig newReset) =
    if idx = setIdx then newReset else idx.getReset aig valid := by
  simp_grind

end setReset

section aig

/-
Aig.addInput' Lemmas.
-/
section addInput'
variable {idx : InputIdx}

@[simp, grind =]
theorem size_addInput' :
    (aig.addInput' idx).size = aig.size + 1 := by
  simp_grind

@[simp, grind =]
theorem numInputs_addInput' :
    (aig.addInput' idx).numInputs =
    if idx.validIn aig then
      aig.numInputs
    else
      aig.numInputs + 1 := by
  simp_defs
  grind [InputIdx.validIn]

@[simp, grind =]
theorem numLatches_addInput' :
    (aig.addInput' idx).numLatches = aig.numLatches := by
  simp_grind

@[simp, grind =]
theorem get_addInput'_self (aig : Aig) :
    (aig.addInput' idx).get (idx.getVar (aig.addInput' idx)) =
    .input idx := by
  simp_grind

end addInput'

/-
Aig.addLatch' Lemmas.
-/
section addLatch'
variable {idx : LatchIdx} {next : Lit} {reset : Option Lit}

@[simp, grind =]
theorem size_addLatch' :
    (aig.addLatch' idx next reset).size = aig.size + 1 := by
  simp_grind

@[simp, grind =]
theorem numInputs_addLatch' :
    (aig.addLatch' idx next reset).numInputs = aig.numInputs := by
  simp_grind

@[simp, grind =]
theorem numLatches_addLatch' :
    (aig.addLatch' idx next reset).numLatches =
    if idx.validIn aig then
      aig.numLatches
    else
      aig.numLatches + 1 := by
  simp_defs
  grind [LatchIdx.validIn]

@[simp, grind =]
theorem get_addLatch'_self :
    (aig.addLatch' idx next reset).get (idx.getVar (aig.addLatch' idx next reset)) =
    .latch idx := by
  simp_grind

@[simp, grind =]
theorem getNext_addLatch'_self :
  idx.getNext (aig.addLatch' idx next reset) = next := by
  simp_grind

@[simp, grind =]
theorem getReset_addLatch'_self :
  idx.getReset (aig.addLatch' idx next reset) = reset := by
  simp_grind

end addLatch'

/-
Aig.addAnd Lemmas.
-/
section addAnd
variable {rhs0 rhs1 : Lit} {h0 : rhs0.validIn aig} {h1 : rhs1.validIn aig}

@[simp, grind .]
theorem size_addAnd :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.size ≥ aig.size := by
  simp_grind

@[simp, grind =]
theorem numInputs_addAnd :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.numInputs = aig.numInputs := by
  simp_grind

@[simp, grind =]
theorem numLatches_addAnd :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.numLatches = aig.numLatches := by
  simp_grind

attribute [local simp, local grind =] Var.validIn_iff in
@[simp]
theorem get_addAnd_new_matches_and {var : Var}
    (notValid : ¬var.validIn aig)
    (valid : var.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst) :
    ∃ (lhs rhs : Lit), (aig.addAnd rhs0 rhs1 h0 h1).fst.get var = .and lhs rhs := by
  simp_all_defs
  split <;> grind [Std.mkAndCached_matches_gate]

end addAnd

end aig
