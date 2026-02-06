module

public import Valaig.Aig.Basic
import all Valaig.Aig.Basic
public import Valaig.Aig.RefValidIn
public import Valaig.Aig.GetSet

public section
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

theorem ResetsValid_of_LatchesValid_AcyclicReset {aig : Aig}
    (latchesValid : aig.LatchesValid)
    (acyclicResets : aig.AcyclicResets) :
    aig.ResetsValid := by
  grind

/--
All indices within the Aig are valid.
-/
@[local grind]
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
@[local grind]
structure WellFormed (aig : Aig) : Prop extends aig.IdxsValid where
  acyclicGates : aig.AcyclicGates
  acyclicResets : aig.AcyclicResets

/-
We consider the same patterns for invariant preservation as in the case of the get/set lemmas
-/

variable {aig : Aig}

/-
Aig.empty Lemmas.
-/
section empty

@[simp]
theorem InputsValid_empty :
    empty.InputsValid := by
  grind

@[simp]
theorem InputIdxsValid_empty :
    empty.InputIdxsValid := by
  grind

@[simp]
theorem LatchesValid_empty :
    empty.LatchesValid := by
  grind

@[simp]
theorem LatchIdxsValid_empty :
    empty.LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_empty :
    empty.ResetsValid := by
  grind

@[simp]
theorem NextsValid_empty :
    empty.NextsValid := by
  grind

@[simp]
theorem AcyclicGates_empty :
    empty.AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_empty :
    empty.AcyclicResets := by
  grind

grind_pattern InputsValid_empty => empty.InputsValid
grind_pattern InputIdxsValid_empty => empty.InputIdxsValid
grind_pattern LatchesValid_empty => empty.LatchesValid
grind_pattern LatchIdxsValid_empty => empty.LatchIdxsValid
grind_pattern ResetsValid_empty => empty.ResetsValid
grind_pattern NextsValid_empty => empty.NextsValid
grind_pattern AcyclicGates_empty => empty.AcyclicGates
grind_pattern AcyclicResets_empty => empty.AcyclicResets

@[simp]
theorem IdxsValid_empty :
    empty.IdxsValid := by
  grind

grind_pattern IdxsValid_empty => empty.IdxsValid

@[simp]
theorem WellFormed_empty :
    empty.WellFormed := by
  grind

grind_pattern WellFormed_empty => empty.WellFormed

end empty

/-
LatchIdx.setNext Lemmas.
-/
section setNext
variable {setIdx : LatchIdx} {setValid : setIdx.validIn aig} {newNext : Lit}

@[simp]
theorem InputsValid_setNext
    (inputsValid : aig.InputsValid) :
    (setIdx.setNext aig newNext setValid).InputsValid := by
  grind

@[simp]
theorem InputIdxsValid_setNext
    (inputIdxsValid : aig.InputIdxsValid) :
    (setIdx.setNext aig newNext setValid).InputIdxsValid := by
  grind

@[simp]
theorem LatchesValid_setNext
    (latchesValid : aig.LatchesValid) :
    (setIdx.setNext aig newNext setValid).LatchesValid := by
  grind

@[simp]
theorem LatchIdxsValid_setNext
    (latchIdxsValid : aig.LatchIdxsValid) :
    (setIdx.setNext aig newNext setValid).LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_setNext
    (resetsValid : aig.ResetsValid) :
    (setIdx.setNext aig newNext setValid).ResetsValid := by
  grind

@[simp]
theorem NextsValid_setNext
    (nextsValid : aig.NextsValid)
    (nextValid : newNext.validIn aig) :
    (setIdx.setNext aig newNext setValid).NextsValid := by
  grind

@[simp]
theorem AcyclicGates_setNext
    (acyclicGates : aig.AcyclicGates) :
    (setIdx.setNext aig newNext setValid).AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_setNext
    (acyclicResets : aig.AcyclicResets) :
    (setIdx.setNext aig newNext setValid).AcyclicResets := by
  grind

-- TODO: These grind patterns could be created with @[grind .], but this seems
-- to spend a lot of compilation time working out the pattern, by doing it
-- manually we avoid this
grind_pattern InputsValid_setNext => (setIdx.setNext aig newNext setValid).InputsValid
grind_pattern InputIdxsValid_setNext => (setIdx.setNext aig newNext setValid).InputIdxsValid
grind_pattern LatchesValid_setNext => (setIdx.setNext aig newNext setValid).LatchesValid
grind_pattern LatchIdxsValid_setNext => (setIdx.setNext aig newNext setValid).LatchIdxsValid
grind_pattern ResetsValid_setNext => (setIdx.setNext aig newNext setValid).ResetsValid
grind_pattern NextsValid_setNext => (setIdx.setNext aig newNext setValid).NextsValid
grind_pattern AcyclicGates_setNext => (setIdx.setNext aig newNext setValid).AcyclicGates
grind_pattern AcyclicResets_setNext => (setIdx.setNext aig newNext setValid).AcyclicResets

@[simp]
theorem IdxsValid_setNext
    (idxsValid : aig.IdxsValid)
    (nextValid : newNext.validIn aig) :
    (setIdx.setNext aig newNext setValid).IdxsValid := by
  grind

grind_pattern IdxsValid_setNext => (setIdx.setNext aig newNext setValid).IdxsValid

@[simp]
theorem WellFormed_setNext
    (wellFormed : aig.WellFormed)
    (nextValid : newNext.validIn aig) :
    (setIdx.setNext aig newNext setValid).WellFormed := by
  grind

grind_pattern WellFormed_setNext => (setIdx.setNext aig newNext setValid).WellFormed

end setNext

/-
LatchIdx.setReset Lemmas.
-/
section setReset
variable {setIdx : LatchIdx} {setValid : setIdx.validIn aig} {newReset : Lit}

@[simp]
theorem InputsValid_setReset
    (inputsValid : aig.InputsValid) :
    (setIdx.setReset aig newReset setValid).InputsValid := by
  grind

@[simp]
theorem InputIdxsValid_setReset
    (inputIdxsValid : aig.InputIdxsValid) :
    (setIdx.setReset aig newReset setValid).InputIdxsValid := by
  grind

@[simp]
theorem LatchesValid_setReset
    (latchesValid : aig.LatchesValid) :
    (setIdx.setReset aig newReset setValid).LatchesValid := by
  grind

@[simp]
theorem LatchIdxsValid_setReset
    (latchIdxsValid : aig.LatchIdxsValid) :
    (setIdx.setReset aig newReset setValid).LatchIdxsValid := by
  grind

@[simp, local grind .]
theorem ResetsValid_of_resetValid_setReset
    (resetsValid : aig.ResetsValid)
    (resetValid : newReset.validIn aig) :
    (setIdx.setReset aig newReset setValid).ResetsValid := by
  grind

@[simp]
theorem ResetsValid_setReset
    (resetsValid : aig.ResetsValid)
    (resetValid : newReset.var < setIdx.getVar aig setValid)
    (varValid : (setIdx.getVar aig setValid).validIn aig) :
    (setIdx.setReset aig newReset setValid).ResetsValid := by
  grind

@[simp]
theorem NextsValid_setReset
    (nextsValid : aig.NextsValid) :
    (setIdx.setReset aig newReset setValid).NextsValid := by
  grind

@[simp]
theorem AcyclicGates_setReset
    (acyclicGates : aig.AcyclicGates) :
    (setIdx.setReset aig newReset setValid).AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_setReset
    (acyclicResets : aig.AcyclicResets)
    (resetValid : newReset.var < setIdx.getVar aig setValid) :
    (setIdx.setReset aig newReset setValid).AcyclicResets := by
  grind

grind_pattern InputsValid_setReset => (setIdx.setReset aig newReset setValid).InputsValid
grind_pattern InputIdxsValid_setReset => (setIdx.setReset aig newReset setValid).InputIdxsValid
grind_pattern LatchesValid_setReset => (setIdx.setReset aig newReset setValid).LatchesValid
grind_pattern LatchIdxsValid_setReset => (setIdx.setReset aig newReset setValid).LatchIdxsValid
grind_pattern ResetsValid_setReset => (setIdx.setReset aig newReset setValid).ResetsValid
grind_pattern NextsValid_setReset => (setIdx.setReset aig newReset setValid).NextsValid
grind_pattern AcyclicGates_setReset => (setIdx.setReset aig newReset setValid).AcyclicGates
grind_pattern AcyclicResets_setReset => (setIdx.setReset aig newReset setValid).AcyclicResets

@[simp]
theorem IdxsValid_setReset
    (idxsValid : aig.IdxsValid)
    (resetValid : newReset.validIn aig) :
    (setIdx.setReset aig newReset setValid).IdxsValid := by
  grind

grind_pattern IdxsValid_setReset => (setIdx.setReset aig newReset setValid).IdxsValid

@[simp]
theorem WellFormed_setReset
    (wellFormed : aig.WellFormed)
    (resetValid : newReset.var < setIdx.getVar aig setValid) :
    (setIdx.setReset aig newReset setValid).WellFormed := by
  grind

grind_pattern WellFormed_setReset => (setIdx.setReset aig newReset setValid).WellFormed

end setReset

/-
Aig.addInput Lemmas.
-/
section addInput

@[simp]
theorem InputsValid_addInput
    (inputsValid : aig.InputsValid) :
    aig.addInput.fst.InputsValid := by
  grind

@[simp]
theorem InputIdxsValid_addInput
    (inputIdxsValid : aig.InputIdxsValid) :
    aig.addInput.fst.InputIdxsValid := by
  grind

@[simp]
theorem LatchesValid_addInput
    (latchesValid : aig.LatchesValid) :
    aig.addInput.fst.LatchesValid := by
  grind

@[simp]
theorem LatchIdxsValid_addInput
    (latchIdxsValid : aig.LatchIdxsValid) :
    aig.addInput.fst.LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_addInput
    (resetsValid : aig.ResetsValid) :
    aig.addInput.fst.ResetsValid := by
  grind

@[simp]
theorem NextsValid_addInput
    (nextsValid : aig.NextsValid) :
    aig.addInput.fst.NextsValid := by
  grind

@[simp]
theorem AcyclicGates_addInput
    (acyclicGates : aig.AcyclicGates) :
    aig.addInput.fst.AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_addInput
    (acyclicResets : aig.AcyclicResets) :
    aig.addInput.fst.AcyclicResets := by
  grind

grind_pattern InputsValid_addInput => aig.addInput.fst.InputsValid
grind_pattern InputIdxsValid_addInput => aig.addInput.fst.InputIdxsValid
grind_pattern LatchesValid_addInput => aig.addInput.fst.LatchesValid
grind_pattern LatchIdxsValid_addInput => aig.addInput.fst.LatchIdxsValid
grind_pattern ResetsValid_addInput => aig.addInput.fst.ResetsValid
grind_pattern NextsValid_addInput => aig.addInput.fst.NextsValid
grind_pattern AcyclicGates_addInput => aig.addInput.fst.AcyclicGates
grind_pattern AcyclicResets_addInput => aig.addInput.fst.AcyclicResets

@[simp]
theorem IdxsValid_addInput
    (idxsValid : aig.IdxsValid) :
    aig.addInput.fst.IdxsValid := by
  grind

grind_pattern IdxsValid_addInput => aig.addInput.fst.IdxsValid

@[simp]
theorem WellFormed_addInput
    (wellFormed : aig.WellFormed) :
    aig.addInput.fst.WellFormed := by
  grind

grind_pattern WellFormed_addInput => aig.addInput.fst.WellFormed

end addInput

/-
Aig.addLatch Lemmas.
-/
section addLatch
variable {next reset : Lit}

@[simp]
theorem InputsValid_addLatch
    (inputsValid : aig.InputsValid) :
    (aig.addLatch next reset).fst.InputsValid := by
  grind

@[simp]
theorem InputIdxsValid_addLatch
    (inputIdxsValid : aig.InputIdxsValid) :
    (aig.addLatch next reset).fst.InputIdxsValid := by
  grind

@[simp]
theorem LatchesValid_addLatch
    (latchesValid : aig.LatchesValid) :
    (aig.addLatch next reset).fst.LatchesValid := by
  grind

@[simp]
theorem LatchIdxsValid_addLatch
    (latchIdxsValid : aig.LatchIdxsValid) :
    (aig.addLatch next reset).fst.LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_addLatch
    (resetsValid : aig.ResetsValid)
    (resetValid : reset.validIn aig) :
    (aig.addLatch next reset).fst.ResetsValid := by
  grind

@[simp]
theorem NextsValid_addLatch
    (nextsValid : aig.NextsValid)
    (nextValid : next.validIn aig) :
    (aig.addLatch next reset).fst.NextsValid := by
  grind

@[simp]
theorem AcyclicGates_addLatch
    (acyclicGates : aig.AcyclicGates) :
    (aig.addLatch next reset).fst.AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_addLatch
    (acyclicResets : aig.AcyclicResets)
    (resetValid : reset.validIn aig) :
    (aig.addLatch next reset).fst.AcyclicResets := by
  grind

grind_pattern InputsValid_addLatch => (aig.addLatch next reset).fst.InputsValid
grind_pattern InputIdxsValid_addLatch => (aig.addLatch next reset).fst.InputIdxsValid
grind_pattern LatchesValid_addLatch => (aig.addLatch next reset).fst.LatchesValid
grind_pattern LatchIdxsValid_addLatch => (aig.addLatch next reset).fst.LatchIdxsValid
grind_pattern ResetsValid_addLatch => (aig.addLatch next reset).fst.ResetsValid
grind_pattern NextsValid_addLatch => (aig.addLatch next reset).fst.NextsValid
grind_pattern AcyclicGates_addLatch => (aig.addLatch next reset).fst.AcyclicGates
grind_pattern AcyclicResets_addLatch => (aig.addLatch next reset).fst.AcyclicResets

@[simp]
theorem IdxsValid_addLatch
    (idxsValid : aig.IdxsValid)
    (resetValid : reset.validIn aig)
    (nextValid : next.validIn aig) :
    (aig.addLatch next reset).fst.IdxsValid := by
  grind

grind_pattern IdxsValid_addLatch => (aig.addLatch next reset).fst.IdxsValid

@[simp]
theorem WellFormed_addLatch
    (wellFormed : aig.WellFormed)
    (resetValid : reset.validIn aig)
    (nextValid : next.validIn aig) :
    (aig.addLatch next reset).fst.WellFormed := by
  grind

grind_pattern WellFormed_addLatch => (aig.addLatch next reset).fst.WellFormed

end addLatch

/-
Aig.addAnd Lemmas.
-/
section addAnd

-- We currently need h0/h1 as the underlying Aig requires it, but this can be
-- removed in the future when using a custom Aig without dependent typing
variable {rhs0 rhs1 : Lit} {h0 : rhs0.validIn aig} {h1 : rhs1.validIn aig}
attribute [local grind <=] get_addAnd_new_matches_and

@[simp]
theorem InputsValid_addAnd
    (inputsValid : aig.InputsValid) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.InputsValid := by
  grind

@[simp]
theorem InputIdxsValid_addAnd
    (inputIdxsValid : aig.InputIdxsValid) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.InputIdxsValid := by
  intro var
  by_cases var.validIn aig
  <;> grind

@[simp]
theorem LatchesValid_addAnd
    (latchesValid : aig.LatchesValid) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.LatchesValid := by
  grind

@[simp]
theorem LatchIdxsValid_addAnd
    (latchIdxsValid : aig.LatchIdxsValid) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.LatchIdxsValid := by
  intro var
  by_cases var.validIn aig
  <;> grind

@[simp]
theorem ResetsValid_addAnd
    (resetsValid : aig.ResetsValid) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.ResetsValid := by
  grind

@[simp]
theorem NextsValid_addAnd
    (nextsValid : aig.NextsValid) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.NextsValid := by
  grind

-- We don't currently need acyclicGates as the underlying AIG maintains this,
-- but we will want it in the future
set_option linter.unusedVariables false in
@[simp]
theorem AcyclicGates_addAnd
    (acyclicGates : aig.AcyclicGates)
    (h0 : rhs0.validIn aig)
    (h1 : rhs1.validIn aig) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.AcyclicGates := by
  simp_all [Var.lt_idx]
  simp [addAnd, get]
  intro var
  have := @Std.Sat.AIG.hdag (i := var.idx)
  grind

@[simp]
theorem AcyclicResets_addAnd
    (acyclicResets : aig.AcyclicResets) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.AcyclicResets := by
  grind

grind_pattern InputsValid_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst.InputsValid
grind_pattern InputIdxsValid_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst.InputIdxsValid
grind_pattern LatchesValid_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst.LatchesValid
grind_pattern LatchIdxsValid_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst.LatchIdxsValid
grind_pattern ResetsValid_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst.ResetsValid
grind_pattern NextsValid_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst.NextsValid
grind_pattern AcyclicGates_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst.AcyclicGates
grind_pattern AcyclicResets_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst.AcyclicResets

@[simp]
theorem IdxsValid_addAnd
    (idxsValid : aig.IdxsValid)
    (h0 : rhs0.validIn aig)
    (h1 : rhs1.validIn aig) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.IdxsValid := by
  grind

grind_pattern IdxsValid_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst.IdxsValid

@[simp]
theorem WellFormed_addAnd
    (idxsValid : aig.WellFormed)
    (h0 : rhs0.validIn aig)
    (h1 : rhs1.validIn aig) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.WellFormed := by
  grind

grind_pattern WellFormed_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst.WellFormed

end addAnd
