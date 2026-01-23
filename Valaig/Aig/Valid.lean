module

public import Valaig.Aig.BasicNew
public import Valaig.Aig.RefsLemmas
import all Valaig.Aig.BasicNew
public import Valaig.Aig.StdSatLemmas

public section pub
namespace Valaig.Aig
variable {aig : Aig}

-- Let grind/simp see inside all the definitions
attribute [local simp, local grind]
  Var.validIn Lit.validIn InputIdx.validIn LatchIdx.validIn GenericIdx.validIn
  InputIdx.setVar InputIdx.getVar
  LatchIdx.setVar LatchIdx.setNext LatchIdx.setReset
  LatchIdx.getVar LatchIdx.getNext LatchIdx.getReset
  Aig.size Aig.addInput Aig.addLatch Aig.addAnd

attribute [local grind] InputIdx LatchIdx
attribute [local grind =_] Var.ext_idx

section input

@[simp, grind =]
theorem InputIdx.setVar_genericIdx_mono (idx : GenericIdx) :
    idx.validIn (setVar input aig var valid) ↔ idx.validIn aig := by
  simp

end input

section latch

@[simp, grind =]
theorem LatchIdx.setVar_genericIdx_mono (idx : GenericIdx) :
    idx.validIn (setVar latch aig var valid) ↔ idx.validIn aig := by
  simp

@[simp, grind =]
theorem LatchIdx.setNext_genericIdx_mono (idx : GenericIdx) :
    idx.validIn (setNext latch aig next valid) ↔ idx.validIn aig := by
  simp

@[simp, grind =]
theorem LatchIdx.setReset_genericIdx_mono (idx : GenericIdx) :
    idx.validIn (setReset latch aig next valid) ↔ idx.validIn aig := by
  simp

end latch

section atom
attribute [local simp, local grind =]
  Std.mkAtom_eq_decls_push Std.mkAtom_size Std.mkAtom_ref_eq_decls_size

/-
addInput Lemmas.
-/

@[grind .]
theorem Aig.addInput_genericIdx_mono_impl (idx : GenericIdx) :
    idx.validIn aig → idx.validIn aig.addInput.fst := by
  simp; grind only

@[simp, grind =]
theorem Aig.addInput_genericIdx_mono (idx : GenericIdx) :
    idx.validIn aig.addInput.fst ↔
    (idx.validIn aig
    ∨ idx = .input aig.addInput.snd
    ∨ idx = .node (aig.addInput.snd.getVar aig.addInput.fst)) := by
  simp; grind

@[grind .]
theorem Aig.addInput_newInput_validIn :
    aig.addInput.snd.validIn aig.addInput.fst := by
  simp

/-
addLatch Lemmas.
-/

@[grind .]
theorem Aig.addLatch_genericIdx_mono_impl (idx : GenericIdx) :
    idx.validIn aig → idx.validIn (aig.addLatch next reset).fst := by
  simp; grind only

@[simp, grind =]
theorem Aig.addLatch_genericIdx_mono (idx : GenericIdx) :
    idx.validIn (aig.addLatch next reset).fst ↔
    (idx.validIn aig
    ∨ idx = .latch (aig.addLatch next reset).snd
    ∨ idx = .node ((aig.addLatch next reset).snd.getVar (aig.addLatch next reset).fst)) := by
  simp; grind

@[grind .]
theorem Aig.addLatch_newLatch_validIn :
    (aig.addLatch next reset).snd.validIn (aig.addLatch next reset).fst := by
  simp

end atom

section gate
attribute [local grind! .] Std.Sat.AIG.mkAndCached_le_size

/-
addAnd Lemmas.
-/

@[grind .]
theorem Aig.addAnd_genericIdx_mono_impl (idx : GenericIdx) :
    idx.validIn aig → idx.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst := by
  simp; grind

@[grind .]
theorem Aig.addAnd_newAnd_validIn :
    (aig.addAnd rhs0 rhs1 h0 h1).snd.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst := by
  simp
  -- TODO: Whycan't I get grind to see this another way
  have {aig : Std.Sat.AIG AtomIdx} {entry: aig.Ref} := entry.hgate
  grind only

end gate

end Valaig.Aig
