module

public meta import Valaig.Prelude
public import Valaig.Aig.Basic
import all Valaig.Aig.Basic
public import Valaig.Aig.Monotone

public section
namespace Valaig.Aig
variable {aig : Aig}

-- General theorems about validity
section

theorem validIn_mono {var var' : Var} (valid : var.validIn aig) (order : var' < var) :
    var'.validIn aig := by
  grind [Var.validIn]

grind_pattern validIn_mono => var.validIn aig, var'.validIn aig, var' < var

@[simp, grind .]
theorem constant_validIn :
    Var.constant.validIn aig := by
  have := aig.aig.hzero
  simpa [Var.validIn]

@[simp, grind .]
theorem false_validIn :
    Lit.false.validIn aig := by
  simp

@[simp, grind .]
theorem true_validIn :
    Lit.true.validIn aig := by
  simp

end

attribute [local simp] Var.validIn Lit.validIn InputIdx.validIn LatchIdx.validIn numInputs numLatches

/-
Aig.empty Lemmas.
-/
section empty

@[simp, grind .]
theorem var_validIn_empty_iff {var : Var} :
    var.validIn empty ↔ var = .constant := by
  simp_defs
  grind [Std.Sat.AIG.empty]

@[simp, grind .]
theorem input_not_validIn_empty {idx : InputIdx} :
    ¬idx.validIn empty := by
  simp_defs

@[simp, grind .]
theorem latch_not_validIn_empty {idx : LatchIdx} :
    ¬idx.validIn empty := by
  simp_defs

end empty

section latch
variable {latch : LatchIdx}

/-
setNext Lemmas.
-/
section setNext
variable {next : Lit}

@[simp, grind =]
theorem var_validIn_setNext_iff {var : Var} :
    var.validIn (latch.setNext aig next) ↔
    var.validIn aig := by
  simp_defs

@[simp, grind =]
theorem input_validIn_setNext_iff {idx : InputIdx} :
    idx.validIn (latch.setNext aig next) ↔
    idx.validIn aig := by
  simp_defs

@[simp, grind =]
theorem latch_validIn_setNext_iff {idx : LatchIdx} :
    idx.validIn (latch.setNext aig next) ↔
    idx.validIn aig := by
  simp_defs

end setNext

/-
setReset Lemmas.
-/
section setReset
variable {reset : Lit}

@[simp, grind =]
theorem var_validIn_setReset_iff {var : Var} :
    var.validIn (latch.setReset aig reset) ↔
    var.validIn aig := by
  simp_defs

@[simp, grind =]
theorem input_validIn_setReset_iff {idx : InputIdx} :
    idx.validIn (latch.setReset aig reset) ↔
    idx.validIn aig := by
  simp_defs

@[simp, grind =]
theorem latch_validIn_setReset_iff {idx : LatchIdx} :
    idx.validIn (latch.setReset aig reset) ↔
    idx.validIn aig := by
  simp_defs

end setReset
end latch

section leaf

/-
addInput' Lemmas.
-/
section addInput'
variable {idx : InputIdx}

@[simp, local grind .]
theorem addInput'_validIn :
    idx.validIn (aig.addInput' idx) := by
  simp_defs

@[simp]
theorem addInput'_getVar_self_validIn :
    idx.getVar (aig.addInput' idx)
    |>.validIn (aig.addInput' idx) := by
  simp_defs

@[simp]
theorem addInput'_getVar_mono {var : Var} (valid : var.validIn aig):
    idx.getVar (aig.addInput' idx) > var := by
  simpa [Var.lt_idx, Std.mkAtom_ref_eq_decls_size, simp_valaig_defs]

grind_pattern addInput'_getVar_mono => idx.getVar (aig.addInput' idx) > var where
  var =/= idx.getVar (aig.addInput' idx)

@[simp, grind =]
theorem var_validIn_addInput'_iff {var : Var} :
    var.validIn (aig.addInput' idx) ↔
      var.validIn aig ∨ var = idx.getVar (aig.addInput' idx) := by
  simp_defs
  grind only

@[simp, grind =]
theorem input_validIn_addInput'_iff {other : InputIdx} :
    other.validIn (aig.addInput' idx)  ↔
     other.validIn aig ∨ idx = other := by
  simp_defs
  grind_defs

@[simp, grind =]
theorem latch_validIn_addInput'_iff {other : LatchIdx} :
    other.validIn (aig.addInput' idx) ↔
    other.validIn aig := by
  simp_defs

end addInput'

/-
addInput Lemmas.
-/
section addInput

@[simp, grind .]
theorem addInput_not_validIn :
    ¬aig.addInput.snd.validIn aig := by
  simp_defs

end addInput

/-
addLatch Lemmas.
-/
section latch
variable {next reset : Lit}

@[simp, local grind .]
theorem addLatch_validIn :
    (aig.addLatch next reset).snd.validIn (aig.addLatch next reset).fst := by
  simp_defs

@[simp]
theorem addLatch_getVar_self_validIn :
    (aig.addLatch next reset).snd.getVar (aig.addLatch next reset).fst
    |>.validIn (aig.addLatch next reset).fst := by
  simp_defs

@[simp]
theorem addLatch_getVar_mono {var : Var} (valid : var.validIn aig):
    (aig.addLatch next reset).snd.getVar (aig.addLatch next reset).fst > var := by
  simpa [Var.lt_idx, Std.mkAtom_ref_eq_decls_size, simp_valaig_defs]

grind_pattern addLatch_getVar_mono => (aig.addLatch next reset).snd.getVar (aig.addLatch next reset).fst > var where
  var =/= (aig.addLatch next reset).snd.getVar (aig.addLatch next reset).fst

@[simp, grind =]
theorem var_validIn_addLatch_iff {var : Var} :
    var.validIn (aig.addLatch next reset).fst  ↔
    (var.validIn aig
    ∨ var = (aig.addLatch next reset).snd.getVar (aig.addLatch next reset).fst) := by
  simp_defs
  grind [Std.mkAtom_ref_eq_decls_size]

@[simp, grind =]
theorem input_validIn_addLatch_iff {idx : InputIdx} :
    idx.validIn (aig.addLatch next reset).fst ↔
    idx.validIn aig := by
  simp_defs

@[simp, grind =]
theorem latch_validIn_addLatch_iff {idx : LatchIdx} :
    idx.validIn (aig.addLatch next reset).fst  ↔
    (idx.validIn aig ∨ idx = (aig.addLatch next reset).snd) := by
  simp_defs
  grind [Std.mkAtom_ref_eq_decls_size, grind_valaig_defs]

end latch
end leaf

/-
addAnd Lemmas.
-/
section gate
variable {rhs0 rhs1 : Lit} {h0 : rhs0.validIn aig} {h1 : rhs1.validIn aig}

@[simp, grind =]
theorem input_validIn_addAnd_iff {idx : InputIdx} :
    idx.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst ↔
    idx.validIn aig := by
  simp_defs

@[simp, grind =]
theorem latch_validIn_addAnd_iff {idx : LatchIdx} :
    idx.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst ↔
    idx.validIn aig := by
  simp_defs

@[simp, grind .]
theorem addAnd_validIn :
    (aig.addAnd rhs0 rhs1 h0 h1).snd.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst := by
  simp_defs
  have {aig : Std.Sat.AIG LeafIdx} {entry : aig.Ref} := entry.hgate
  grind only

end gate
