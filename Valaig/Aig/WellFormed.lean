module

public import Valaig.Aig.BasicNew
import all Valaig.Aig.BasicNew
public import Valaig.Aig.IdxValidity

public section pub
namespace Valaig.Aig

setup_get_set_definitions

/--
All input indices point to an input in the Aig.
-/
@[expose, simp]
def InputsValid (aig : Aig) : Prop :=
  ∀ {idx : InputIdx} (valid : idx.validIn aig),
  ∃ (valid' : (idx.getVar aig valid).validIn aig),
    aig[idx.getVar aig valid] = .input idx

/--
All inputs in the Aig point to a corresponding input index.
-/
def InputIdxsValid (aig : Aig) : Prop :=
  ∀ {var : Var} (valid : var.validIn aig),
  match aig[var] with
  | .input idx =>
    ∃ (valid' : idx.validIn aig), idx.getVar aig valid' = var
  | _ => True

/--
All latch indices point to a latch in the Aig.
-/
@[expose, simp]
def LatchesValid (aig : Aig) : Prop :=
  ∀ {idx : LatchIdx} (valid : idx.validIn aig),
  ∃ (valid' : (idx.getVar aig valid).validIn aig),
    aig[idx.getVar aig valid] = .latch idx

/--
All latches in the Aig point to a corresponding latch index.
-/
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
@[expose, simp]
def ResetsValid (aig : Aig) : Prop :=
  ∀ {idx : LatchIdx} (valid : idx.validIn aig),
    (idx.getReset aig valid).validIn aig

/--
All latch next state literals are valid in the Aig.
-/
@[expose, simp]
def NextsValid (aig : Aig) : Prop :=
  ∀ {idx : LatchIdx} (valid : idx.validIn aig),
    (idx.getNext aig valid).validIn aig

/--
The gates of the Aig are acyclic.
This is enforced by requiring each gate's inputs to have lower variable
indices than themselves.
-/
@[expose, simp]
def AcyclicGates (aig : Aig) : Prop :=
  ∀ {var : Var} {rhs0 rhs1} (valid : var.validIn aig),
    aig[var] = .and rhs0 rhs1 → rhs0.var < var ∧ rhs1.var < var

/--
The reset function of the Aig is acyclic.
This is enfoced by requiring each latch's reset to have a lower variable
index than the latch's output.
-/
@[expose, simp]
def AcyclicResets (aig : Aig) : Prop :=
  ∀ {idx : LatchIdx} (valid : idx.validIn aig),
    (idx.getReset aig valid).var < idx.getVar aig valid

@[local grind]
structure WellFormed (aig : Aig) : Prop where
  inputsValid : aig.InputsValid
  inputIdxsValid : aig.InputIdxsValid

  -- ResetsValid isn't included as it follows from latchesValid and acyclicReset
  latchesValid : aig.LatchesValid
  latchIdxsValid : aig.LatchIdxsValid
  nextsValid : aig.NextsValid

  acyclicGates : aig.AcyclicGates
  acyclicReset : aig.AcyclicResets

@[grind .]
theorem WellFormed.resetsValid {aig : Aig} (wf : aig.WellFormed) :
    aig.ResetsValid := by
  intro _ valid
  rcases wf.latchesValid valid with ⟨varValid, _⟩
  have resetLt := wf.acyclicReset valid
  exact validIn_mono varValid resetLt

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
theorem AcyclicGates_InputIdx_setNext (acyclicGates : aig.AcyclicGates) :
    (setIdx.setNext aig newNext setValid).AcyclicGates := by
  simp_all; assumption

@[grind .]
theorem AcyclicResets_InputIdx_setNext (acyclicResets : aig.AcyclicResets) :
    (setIdx.setNext aig newNext setValid).AcyclicResets := by
  simp_all; grind

@[grind .]
theorem WellFormed_InputIdx_setNext (wellFormed : aig.WellFormed) :
    (setIdx.setNext aig newNext setValid).WellFormed := by
  constructor <;> sorry -- grind

end setNext

/-
LatchIdx.setReset Lemmas.
-/
section setReset
variable {setIdx : LatchIdx} {setValid : setIdx.validIn aig} {newReset : Lit}

@[grind .]
theorem AcyclicGates_InputIdx_setReset (acyclicGates : aig.AcyclicGates) :
    (setIdx.setReset aig newReset setValid).AcyclicGates := by
  simp_all; assumption

@[grind .]
theorem AcyclicResets_InputIdx_setReset (acyclicResets : aig.AcyclicResets)
    (acyclic : newReset.var < setIdx.getVar aig setValid) :
    (setIdx.setReset aig newReset setValid).AcyclicResets := by
  simp_all; grind

@[grind .]
theorem WellFormed_InputIdx_setReset (wellFormed : aig.WellFormed)
    (acyclic : newReset.var < setIdx.getVar aig setValid) :
    (setIdx.setReset aig newReset setValid).WellFormed := by
  constructor <;> sorry -- grind

end setReset

/-
Aig.addInput Lemmas.
-/
section addInput

@[grind .]
theorem AcyclicGates_Aig_addInput (acyclicGates : aig.AcyclicGates) :
    aig.addInput.fst.AcyclicGates := by
  simp_all; grind

@[grind .]
theorem AcyclicResets_Aig_addInput (acyclicResets : aig.AcyclicResets) :
    aig.addInput.fst.AcyclicResets := by
  simp_all

@[grind .]
theorem WellFormed_Aig_addInput (wellFormed : aig.WellFormed) :
    aig.addInput.fst.WellFormed := by
  constructor <;> sorry -- grind

end addInput

/-
Aig.addLatch Lemmas.
-/
section addLatch
variable {next reset : Lit}

@[grind .]
theorem AcyclicGates_Aig_addLatch (acyclicGates : aig.AcyclicGates) :
    (aig.addLatch next reset).fst.AcyclicGates := by
  simp_all; grind

@[grind .]
theorem AcyclicResets_Aig_addLatch (acyclicResets : aig.AcyclicResets)
    (resetValid : reset.validIn aig) :
    (aig.addLatch next reset).fst.AcyclicResets := by
  simp_all; grind [Var.lt_idx, Lit.validIn, Var.validIn]

@[grind .]
theorem WellFormed_Aig_addLatch (wellFormed : aig.WellFormed)
    (resetValid : reset.validIn aig) :
    (aig.addLatch next reset).fst.WellFormed := by
  constructor <;> sorry -- grind

end addLatch

/-
Aig.addAnd Lemmas.
-/
section addAnd
variable {rhs0 rhs1 : Lit}

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
  grind

@[grind .]
theorem AcyclicResets_Aig_addAnd (acyclicResets : aig.AcyclicResets) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.AcyclicResets := by
  simp_all

@[grind .]
theorem WellFormed_Aig_addAnd (wellFormed : aig.WellFormed) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.WellFormed := by
  constructor <;> sorry -- grind

end addAnd
