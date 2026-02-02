module

public import Valaig.Aig.BasicNew
import all Valaig.Aig.BasicNew

public section pub
namespace Valaig.Aig
variable {aig : Aig}

-- Let grind/simp see inside all the definitions
setup_get_set_definitions
attribute [local simp, local grind]
  Var.validIn Lit.validIn InputIdx.validIn LatchIdx.validIn GenericIdx.validIn

-- General theorems about validity
section

theorem validIn_mono {var var' : Var} (valid : var.validIn aig) (order : var' < var) :
    var'.validIn aig := by
  grind [Var.lt_idx]

end

section latch
variable {latch : LatchIdx} {valid : latch.validIn aig}

@[simp, grind =]
theorem LatchIdx.validIn_setNext {next : Lit} (idx : GenericIdx) :
    idx.validIn (setNext latch aig next valid) ↔ idx.validIn aig := by
  simp

@[simp, grind =]
theorem LatchIdx.validIn_setReset {reset : Lit} (idx : GenericIdx) :
    idx.validIn (setReset latch aig reset valid) ↔ idx.validIn aig := by
  simp

end latch

section atom

/-
addInput Lemmas.
-/

theorem validIn_addInput (idx : GenericIdx) :
    idx.validIn aig → idx.validIn aig.addInput.fst := by
  simp; grind only

grind_pattern validIn_addInput => idx.validIn aig.addInput.fst where
  idx =/= .input aig.addInput.snd
  idx =/= .node (aig.addInput.snd.getVar aig.addInput.fst)

@[simp, grind .]
theorem addInput_validIn :
    aig.addInput.snd.validIn aig.addInput.fst := by
  simp

@[simp, grind .]
theorem addInput_getVar_validIn :
    (aig.addInput.snd.getVar aig.addInput.fst).validIn aig.addInput.fst := by
  simp

/-
addLatch Lemmas.
-/
section latch
variable {next reset : Lit}

theorem validIn_addLatch (idx : GenericIdx) :
    idx.validIn aig → idx.validIn (aig.addLatch next reset).fst := by
  simp; grind only

grind_pattern validIn_addLatch => idx.validIn (aig.addLatch next reset).fst where
  idx =/= .latch (aig.addLatch next reset).snd
  idx =/= .node ((aig.addLatch next reset).snd.getVar (aig.addLatch next reset).fst)

@[simp, grind .]
theorem addLatch_validIn :
    (aig.addLatch next reset).snd.validIn (aig.addLatch next reset).fst := by
  simp

@[simp, grind .]
theorem addLatch_getVar_validIn :
    (aig.addLatch next reset).snd.getVar (aig.addLatch next reset).fst |>.validIn
      (aig.addLatch next reset).fst := by
  simp

end latch
end atom

/-
addAnd Lemmas.
-/
section gate
variable {rhs0 rhs1 : Lit} {h0 : rhs0.validIn aig} {h1 : rhs1.validIn aig}

theorem validIn_addAnd (idx : GenericIdx) :
    idx.validIn aig → idx.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst := by
  simp; grind

grind_pattern validIn_addAnd => idx.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst where
  idx =/= .node (aig.addAnd rhs0 rhs1 h0 h1).snd.var

@[simp, grind .]
theorem addAnd_validIn :
    (aig.addAnd rhs0 rhs1 h0 h1).snd.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst := by
  simp
  have {aig : Std.Sat.AIG AtomIdx} {entry: aig.Ref} := entry.hgate
  grind only

end gate
