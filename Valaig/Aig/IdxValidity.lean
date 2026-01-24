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

section latch
variable {latch : LatchIdx} {valid : latch.validIn aig}

@[simp, grind =]
theorem LatchIdx.setNext_genericIdx_mono {next : Lit} (idx : GenericIdx) :
    idx.validIn (setNext latch aig next valid) ↔ idx.validIn aig := by
  simp

@[simp, grind =]
theorem LatchIdx.setReset_genericIdx_mono {reset : Lit} (idx : GenericIdx) :
    idx.validIn (setReset latch aig reset valid) ↔ idx.validIn aig := by
  simp

end latch

section atom

/-
addInput Lemmas.
-/

@[grind .]
theorem addInput_genericIdx_mono_impl (idx : GenericIdx) :
    idx.validIn aig → idx.validIn aig.addInput.fst := by
  simp; grind only

@[simp, grind =]
theorem addInput_genericIdx_mono (idx : GenericIdx) :
    idx.validIn aig.addInput.fst ↔
    (idx.validIn aig
    ∨ idx = .input aig.addInput.snd
    ∨ idx = .node (aig.addInput.snd.getVar aig.addInput.fst)) := by
  simp; grind

@[grind .]
theorem addInput_self_validIn :
    aig.addInput.snd.validIn aig.addInput.fst := by
  simp

/-
addLatch Lemmas.
-/
section latch
variable {next reset : Lit}

@[grind .]
theorem addLatch_genericIdx_mono_impl (idx : GenericIdx) :
    idx.validIn aig → idx.validIn (aig.addLatch next reset).fst := by
  simp; grind only

@[simp, grind =]
theorem addLatch_genericIdx_mono (idx : GenericIdx) :
    idx.validIn (aig.addLatch next reset).fst ↔
    (idx.validIn aig
    ∨ idx = .latch (aig.addLatch next reset).snd
    ∨ idx = .node ((aig.addLatch next reset).snd.getVar (aig.addLatch next reset).fst)) := by
  simp; grind

@[grind .]
theorem addLatch_self_validIn :
    (aig.addLatch next reset).snd.validIn (aig.addLatch next reset).fst := by
  simp

end latch
end atom

/-
addAnd Lemmas.
-/
section gate
variable {rhs0 rhs1 : Lit} {h0 : rhs0.validIn aig} {h1 : rhs1.validIn aig}

@[grind .]
theorem addAnd_genericIdx_mono_impl (idx : GenericIdx) :
    idx.validIn aig → idx.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst := by
  simp; grind

@[grind .]
theorem addAnd_self_validIn :
    (aig.addAnd rhs0 rhs1 h0 h1).snd.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst := by
  simp
  -- TODO: Whycan't I get grind to see this another way
  have {aig : Std.Sat.AIG AtomIdx} {entry: aig.Ref} := entry.hgate
  grind only

end gate
