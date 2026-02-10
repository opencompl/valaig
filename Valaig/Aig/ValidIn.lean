module

public meta import Valaig.Prelude
public import Valaig.Aig.Basic
import all Valaig.Aig.Basic

public section
namespace Valaig.Aig
variable {aig : Aig}

attribute [local simp, local grind] Var.validIn Lit.validIn InputIdx.validIn LatchIdx.validIn
attribute [local grind =_] Var.ext_idx

-- General theorems about validity
section

theorem validIn_mono {var var' : Var} (valid : var.validIn aig) (order : var' < var) :
    var'.validIn aig := by
  simp_all_defs
  grind [Var.lt_idx]

grind_pattern validIn_mono => var.validIn aig, var'.validIn aig, var' < var

@[simp, grind .]
theorem constant_validIn :
    Var.constant.validIn aig := by
  have := aig.aig.hzero
  simp [Var.constant_idx_eq_zero]
  grind_defs

end

/-
Aig.empty Lemmas.
-/
section empty

@[simp, grind .]
theorem input_not_validIn_empty {idx : InputIdx} :
    ¬idx.validIn empty := by
  simp_defs

@[simp, grind .]
theorem latch_not_validIn_empty {idx : LatchIdx} :
    ¬idx.validIn empty := by
  simp_defs

@[simp, grind .]
theorem var_validIn_empty_iff_eq_constant {var : Var} :
    var.validIn empty ↔ var = .constant := by
  simp_defs
  simp [Var.ext_idx, Var.constant_idx_eq_zero, Std.Sat.AIG.empty]

end empty

section latch
variable {latch : LatchIdx} {valid : latch.validIn aig}

/-
setNext Lemmas.
-/
section setNext
variable {next : Lit}

@[simp, grind =]
theorem input_validIn_setNext_iff {idx : InputIdx} :
    idx.validIn (latch.setNext aig next valid) ↔
    idx.validIn aig := by
  simp_defs

@[simp, grind =]
theorem latch_validIn_setNext_iff {idx : LatchIdx} :
    idx.validIn (latch.setNext aig next valid) ↔
    idx.validIn aig := by
  simp_defs

@[simp, grind =]
theorem var_validIn_setNext_iff {var : Var} :
    var.validIn (latch.setNext aig next valid) ↔
    var.validIn aig := by
  simp_defs

end setNext

/-
setReset Lemmas.
-/
section setReset
variable {reset : Lit}

@[simp, grind =]
theorem input_validIn_setReset_iff {idx : InputIdx} :
    idx.validIn (latch.setReset aig reset valid) ↔
    idx.validIn aig := by
  simp_defs

@[simp, grind =]
theorem latch_validIn_setReset_iff {idx : LatchIdx} :
    idx.validIn (latch.setReset aig reset valid) ↔
    idx.validIn aig := by
  simp_defs

@[simp, grind =]
theorem var_validIn_setReset_iff {var : Var} :
    var.validIn (latch.setReset aig reset valid) ↔
    var.validIn aig := by
  simp_defs

end setReset
end latch

section atom

/-
addInput Lemmas.
-/

@[simp, local grind .]
theorem addInput_validIn :
    aig.addInput.snd.validIn aig.addInput.fst := by
  simp_defs

@[simp]
theorem addInput_getVar_self_validIn :
    aig.addInput.snd.getVar aig.addInput.fst
    |>.validIn aig.addInput.fst := by
  simp_defs

@[simp]
theorem addInput_getVar_mono {var : Var} (valid : var.validIn aig):
    aig.addInput.snd.getVar aig.addInput.fst > var := by
  simpa [Var.lt_idx, Std.mkAtom_ref_eq_decls_size, simp_valaig_defs]

grind_pattern addInput_getVar_mono =>
  var.validIn aig, aig.addInput.snd.getVar aig.addInput.fst where
  var =/= aig.addInput.snd.getVar aig.addInput.fst

@[simp, grind =]
theorem input_validIn_addInput_iff {idx : InputIdx} :
    idx.validIn aig.addInput.fst  ↔
    (idx.validIn aig ∨ idx = aig.addInput.snd) := by
  simp_defs
  grind [Std.mkAtom_ref_eq_decls_size, grind_valaig_defs]

@[simp, grind =]
theorem latch_validIn_addInput_iff {idx : LatchIdx} :
    idx.validIn aig.addInput.fst ↔
    idx.validIn aig := by
  simp_defs

@[simp, grind =]
theorem var_validIn_addInput_iff {var : Var} :
    var.validIn aig.addInput.fst  ↔
    (var.validIn aig ∨ var = aig.addInput.snd.getVar aig.addInput.fst) := by
  simp_defs
  grind [Std.mkAtom_ref_eq_decls_size]

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

grind_pattern addLatch_getVar_mono =>
  var.validIn aig, (aig.addLatch next reset).snd.getVar (aig.addLatch next reset).fst where
  var =/= (aig.addLatch next reset).snd.getVar (aig.addLatch next reset).fst

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

@[simp, grind =]
theorem var_validIn_addLatch_iff {var : Var} :
    var.validIn (aig.addLatch next reset).fst  ↔
    (var.validIn aig
    ∨ var = (aig.addLatch next reset).snd.getVar (aig.addLatch next reset).fst) := by
  simp_defs
  grind [Std.mkAtom_ref_eq_decls_size]

end latch
end atom

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
theorem var_validIn_addAnd {var : Var} :
    var.validIn aig → var.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst := by
  grind_defs

@[simp, grind .]
theorem addAnd_validIn :
    (aig.addAnd rhs0 rhs1 h0 h1).snd.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst := by
  simp_defs
  have {aig : Std.Sat.AIG AtomIdx} {entry: aig.Ref} := entry.hgate
  grind only

end gate
