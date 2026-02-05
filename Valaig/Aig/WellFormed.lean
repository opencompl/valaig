module

public import Valaig.Aig.BasicNew
import all Valaig.Aig.BasicNew
public import Valaig.Aig.IdxValidity
public import Valaig.Aig.GetSet

public section pub
namespace Valaig.Aig

/--
All input indices point to an input in the Aig.
-/
@[expose, grind, local simp]
def InputsValid (aig : Aig) : Prop :=
  ∀ {idx : InputIdx} (valid : idx.validIn aig),
  ∃ (valid' : (idx.getVar aig valid).validIn aig),
    aig[idx.getVar aig valid] = .input idx

/--
All inputs in the Aig point to a corresponding input index.
-/
@[expose, grind, local simp]
def InputIdxsValid (aig : Aig) : Prop :=
  ∀ {var : Var} (valid : var.validIn aig),
  match aig[var] with
  | .input idx =>
    ∃ (valid' : idx.validIn aig), idx.getVar aig valid' = var
  | _ => True

/--
All latch indices point to a latch in the Aig.
-/
@[expose, grind, local simp]
def LatchesValid (aig : Aig) : Prop :=
  ∀ {idx : LatchIdx} (valid : idx.validIn aig),
  ∃ (valid' : (idx.getVar aig valid).validIn aig),
    aig[idx.getVar aig valid] = .latch idx

/--
All latches in the Aig point to a corresponding latch index.
-/
@[expose, grind, local simp]
def LatchIdxsValid (aig : Aig) : Prop :=
  ∀ {var : Var} (valid : var.validIn aig),
  match aig[var] with
  | .latch idx =>
    ∃ (valid' : idx.validIn aig), idx.getVar aig valid' = var
  | _ => True

/--
All latch reset literals are valid in the Aig.
This follows from `LatchesValid` and `AcyclicResets`.
-/
@[expose, grind, local simp]
def ResetsValid (aig : Aig) : Prop :=
  ∀ {idx : LatchIdx} (valid : idx.validIn aig),
    (idx.getReset aig valid).validIn aig

/--
All latch next state literals are valid in the Aig.
-/
@[expose, grind, local simp]
def NextsValid (aig : Aig) : Prop :=
  ∀ {idx : LatchIdx} (valid : idx.validIn aig),
    (idx.getNext aig valid).validIn aig

/--
The gates of the Aig are acyclic.
This is enforced by requiring each gate's inputs to have lower variable
indices than themselves.
-/
@[expose, grind, local simp]
def AcyclicGates (aig : Aig) : Prop :=
  ∀ {var : Var} {rhs0 rhs1} (valid : var.validIn aig),
    aig[var] = .and rhs0 rhs1 → rhs0.var < var ∧ rhs1.var < var

/--
The reset function of the Aig is acyclic.
This is enfoced by requiring each latch's reset to have a lower variable
index than the latch's output.
-/
@[expose, grind, local simp]
def AcyclicResets (aig : Aig) : Prop :=
  ∀ {idx : LatchIdx} (valid : idx.validIn aig),
    (idx.getReset aig valid).var < idx.getVar aig valid

@[grind .]
theorem ResetsValid_of_LatchesValid_AcyclicReset {aig : Aig}
    (latchesValid : aig.LatchesValid)
    (acyclicResets : aig.AcyclicResets) :
    aig.ResetsValid := by
  grind

/--
All indices within the Aig are valid.
-/
@[grind]
structure IdxsValid (aig : Aig) : Prop where
  inputsValid : aig.InputsValid
  inputIdxsValid : aig.InputIdxsValid

  latchesValid : aig.LatchesValid
  latchIdxsValid : aig.LatchIdxsValid
  resetsValid : aig.ResetsValid
  nextsValid : aig.NextsValid

/--
All indices within the Aig are valid and the gates and reset function are
acyclic, allowing the definition of semantics
@[grind]
-/
@[grind]
structure WellFormed (aig : Aig) : Prop extends aig.IdxsValid where
  acyclicGates : aig.AcyclicGates
  acyclicResets : aig.AcyclicResets

/-
We consider the same patterns for invariant preservation as in the case of the get/set lemmas
-/

variable {aig : Aig}

/-
LatchIdx.setNext Lemmas.
-/
section setNext
variable {setIdx : LatchIdx} {setValid : setIdx.validIn aig} {newNext : Lit}

@[grind .]
theorem setNext_InputsValid
    (inputsValid : aig.InputsValid) :
    (setIdx.setNext aig newNext setValid).InputsValid := by
  grind

@[grind .]
theorem setNext_InputIdxsValid
    (inputIdxsValid : aig.InputIdxsValid) :
    (setIdx.setNext aig newNext setValid).InputIdxsValid := by
  grind

@[grind .]
theorem setNext_LatchesValid
    (latchesValid : aig.LatchesValid) :
    (setIdx.setNext aig newNext setValid).LatchesValid := by
  grind

@[grind .]
theorem setNext_LatchIdxsValid
    (latchIdxsValid : aig.LatchIdxsValid) :
    (setIdx.setNext aig newNext setValid).LatchIdxsValid := by
  grind

@[grind .]
theorem setNext_ResetsValid
    (resetsValid : aig.ResetsValid) :
    (setIdx.setNext aig newNext setValid).ResetsValid := by
  grind

@[grind .]
theorem setNext_NextsValid
    (nextsValid : aig.NextsValid)
    (nextValid : newNext.validIn aig) :
    (setIdx.setNext aig newNext setValid).NextsValid := by
  grind

@[grind .]
theorem setNext_AcyclicGates
    (acyclicGates : aig.AcyclicGates) :
    (setIdx.setNext aig newNext setValid).AcyclicGates := by
  grind

@[grind .]
theorem setNext_AcyclicResets
    (acyclicResets : aig.AcyclicResets) :
    (setIdx.setNext aig newNext setValid).AcyclicResets := by
  grind

@[grind .]
theorem setNext_IdxsValid
    (idxsValid : aig.IdxsValid)
    (nextValid : newNext.validIn aig) :
    (setIdx.setNext aig newNext setValid).IdxsValid := by
  grind

@[grind .]
theorem setNext_WellFormed
    (wellFormed : aig.WellFormed)
    (nextValid : newNext.validIn aig) :
    (setIdx.setNext aig newNext setValid).WellFormed := by
  grind

end setNext

/-
LatchIdx.setReset Lemmas.
-/
section setReset
variable {setIdx : LatchIdx} {setValid : setIdx.validIn aig} {newReset : Lit}

@[grind .]
theorem setReset_InputsValid
    (inputsValid : aig.InputsValid) :
    (setIdx.setReset aig newReset setValid).InputsValid := by
  grind

@[grind .]
theorem setReset_InputIdxsValid
    (inputIdxsValid : aig.InputIdxsValid) :
    (setIdx.setReset aig newReset setValid).InputIdxsValid := by
  grind

@[grind .]
theorem setReset_LatchesValid
    (latchesValid : aig.LatchesValid) :
    (setIdx.setReset aig newReset setValid).LatchesValid := by
  grind

@[grind .]
theorem setReset_LatchIdxsValid
    (latchIdxsValid : aig.LatchIdxsValid) :
    (setIdx.setReset aig newReset setValid).LatchIdxsValid := by
  grind

@[grind .]
theorem setReset_ResetsValid_of_resetValid
    (resetsValid : aig.ResetsValid)
    (resetValid : newReset.validIn aig) :
    (setIdx.setReset aig newReset setValid).ResetsValid := by
  grind

@[grind .]
theorem setReset_ResetsValid
    (resetsValid : aig.ResetsValid)
    (resetValid : newReset.var < setIdx.getVar aig setValid)
    (varValid : (setIdx.getVar aig setValid).validIn aig) :
    (setIdx.setReset aig newReset setValid).ResetsValid := by
  grind

@[grind .]
theorem setReset_NextsValid
    (nextsValid : aig.NextsValid) :
    (setIdx.setReset aig newReset setValid).NextsValid := by
  grind

@[grind .]
theorem setReset_AcyclicGates
    (acyclicGates : aig.AcyclicGates) :
    (setIdx.setReset aig newReset setValid).AcyclicGates := by
  grind

@[grind .]
theorem setReset_AcyclicResets
    (acyclicResets : aig.AcyclicResets)
    (resetValid : newReset.var < setIdx.getVar aig setValid) :
    (setIdx.setReset aig newReset setValid).AcyclicResets := by
  grind

@[grind .]
theorem setReset_IdxsValid
    (idxsValid : aig.IdxsValid)
    (resetValid : newReset.validIn aig) :
    (setIdx.setReset aig newReset setValid).IdxsValid := by
  grind

@[grind .]
theorem setReset_WellFormed
    (wellFormed : aig.WellFormed)
    (resetValid : newReset.var < setIdx.getVar aig setValid) :
    (setIdx.setReset aig newReset setValid).WellFormed := by
  grind

end setReset

/-
Aig.addInput Lemmas.
-/
section addInput

@[grind .]
theorem addInput_InputsValid
    (inputsValid : aig.InputsValid) :
    aig.addInput.fst.InputsValid := by
  grind

@[grind .]
theorem addInput_InputIdxsValid
    (inputIdxsValid : aig.InputIdxsValid) :
    aig.addInput.fst.InputIdxsValid := by
  grind

@[grind .]
theorem addInput_LatchesValid
    (latchesValid : aig.LatchesValid) :
    aig.addInput.fst.LatchesValid := by
  grind

@[grind .]
theorem addInput_LatchIdxsValid
    (latchIdxsValid : aig.LatchIdxsValid) :
    aig.addInput.fst.LatchIdxsValid := by
  grind

@[grind .]
theorem addInput_ResetsValid
    (resetsValid : aig.ResetsValid) :
    aig.addInput.fst.ResetsValid := by
  grind

@[grind .]
theorem addInput_NextsValid
    (nextsValid : aig.NextsValid) :
    aig.addInput.fst.NextsValid := by
  grind

@[grind .]
theorem addInput_AcyclicGates
    (acyclicGates : aig.AcyclicGates) :
    aig.addInput.fst.AcyclicGates := by
  grind

@[grind .]
theorem addInput_AcyclicResets
    (acyclicResets : aig.AcyclicResets) :
    aig.addInput.fst.AcyclicResets := by
  grind

@[grind .]
theorem addInput_IdxsValid
    (idxsValid : aig.IdxsValid) :
    aig.addInput.fst.IdxsValid := by
  grind

@[grind .]
theorem addInput_WellFormed
    (wellFormed : aig.WellFormed) :
    aig.addInput.fst.WellFormed := by
  grind

end addInput

/-
Aig.addLatch Lemmas.
-/
section addLatch
variable {next reset : Lit}

@[grind .]
theorem addLatch_InputsValid
    (inputsValid : aig.InputsValid) :
    (aig.addLatch next reset).fst.InputsValid := by
  grind

@[grind .]
theorem addLatch_InputIdxsValid
    (inputIdxsValid : aig.InputIdxsValid) :
    (aig.addLatch next reset).fst.InputIdxsValid := by
  grind

@[grind .]
theorem addLatch_LatchesValid
    (latchesValid : aig.LatchesValid) :
    (aig.addLatch next reset).fst.LatchesValid := by
  grind

@[grind .]
theorem addLatch_LatchIdxsValid
    (latchIdxsValid : aig.LatchIdxsValid) :
    (aig.addLatch next reset).fst.LatchIdxsValid := by
  grind

@[grind .]
theorem addLatch_ResetsValid
    (resetsValid : aig.ResetsValid)
    (resetValid : reset.validIn aig) :
    (aig.addLatch next reset).fst.ResetsValid := by
  grind

@[grind .]
theorem addLatch_NextsValid
    (nextsValid : aig.NextsValid)
    (nextValid : next.validIn aig) :
    (aig.addLatch next reset).fst.NextsValid := by
  grind

@[grind .]
theorem addLatch_AcyclicGates
    (acyclicGates : aig.AcyclicGates) :
    (aig.addLatch next reset).fst.AcyclicGates := by
  grind

@[grind .]
theorem addLatch_AcyclicResets
    (acyclicResets : aig.AcyclicResets)
    (resetValid : reset.validIn aig) :
    (aig.addLatch next reset).fst.AcyclicResets := by
  grind

@[grind .]
theorem addLatch_IdxsValid
    (idxsValid : aig.IdxsValid)
    (resetValid : reset.validIn aig)
    (nextValid : next.validIn aig) :
    (aig.addLatch next reset).fst.IdxsValid := by
  grind

@[grind .]
theorem addLatch_WellFormed
    (wellFormed : aig.WellFormed)
    (resetValid : reset.validIn aig)
    (nextValid : next.validIn aig) :
    (aig.addLatch next reset).fst.WellFormed := by
  grind

end addLatch

/-
Aig.addAnd Lemmas.
-/
section addAnd
variable {rhs0 rhs1 : Lit}

set_option warn.sorry false

-- We don't currently need acyclicGates as the underlying AIG maintains this, but we will want it
-- in the future
set_option linter.unusedVariables false in
@[grind .]
theorem AcyclicGates_Aig_addAnd (acyclicGates : aig.AcyclicGates)
    (h0 : rhs0.validIn aig) (h1 : rhs1.validIn aig) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.AcyclicGates := by
  simp_all [Var.validIn, Var.lt_idx]
  intro var
  have := @Std.Sat.AIG.hdag (i := var.idx)
  sorry

@[grind .]
theorem AcyclicResets_Aig_addAnd (acyclicResets : aig.AcyclicResets) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.AcyclicResets := by
  sorry

@[grind .]
theorem WellFormed_Aig_addAnd (wellFormed : aig.WellFormed) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.WellFormed := by
  constructor <;> sorry -- grind

end addAnd
