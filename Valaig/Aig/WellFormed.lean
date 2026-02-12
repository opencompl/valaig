module

import all Valaig.Aig.Basic
public import Valaig.Aig.GetSet

public section
namespace Valaig.Aig

variable {aig : Aig}

/-
To try to prevent too much pollution of grind patterns, we try to set up the following strategy:
- WellFormed and individual wellformedness predicates (e.g. InputsValid) should automatically
  propagate forwards and backwards over terms preserving them, however WellFormed should not
  automatically cast to individual predicates.
- Specific uses of each predicate are defined as theorems that require that predicate as argument
  and match on specific outputs.
- Theorems to bridge from WellFormed to each predicate exist but are only triggered if both
  parts appear (as should have been triggered by the above rules).
-/

/--
All input indices point to an input in the Aig.
-/
@[expose, local grind, local simp]
def InputsValid (aig : Aig) : Prop :=
  ∀ {idx : InputIdx} (valid : idx.validIn aig),
  ∃ (valid' : (idx.getVar aig valid).validIn aig),
    aig.get (idx.getVar aig valid) valid' = .input idx

@[simp]
theorem input_getVar_validIn {inputsValid : aig.InputsValid} {idx : InputIdx} (valid : idx.validIn aig) :
    idx.getVar aig valid |>.validIn aig := by
  grind

grind_pattern input_getVar_validIn => idx.getVar aig valid |>.validIn aig

@[simp]
theorem get_input_getVar {inputsValid : aig.InputsValid} {idx : InputIdx} (valid : idx.validIn aig) :
    aig.get (idx.getVar aig valid) = .input idx := by
  grind

grind_pattern get_input_getVar => aig.get (idx.getVar aig valid)

/--
All inputs in the Aig point to a corresponding input index.
-/
@[expose, local grind, local simp]
def InputIdxsValid (aig : Aig) : Prop :=
  ∀ {var : Var} (valid : var.validIn aig),
  match aig.get var valid with
  | .input idx =>
    ∃ (valid' : idx.validIn aig), idx.getVar aig valid' = var
  | _ => true

@[simp]
theorem validIn_of_get_eq_input {inputIdxsValid : aig.InputIdxsValid} {var : Var} {idx : InputIdx}
    (valid : var.validIn aig) (eq : aig.get var valid = .input idx) :
    idx.validIn aig := by
  grind

grind_pattern validIn_of_get_eq_input => idx.validIn aig, Node.input idx, aig.get var valid

@[simp]
theorem input_getVar_get {inputIdxsValid : aig.InputIdxsValid} {var : Var} {idx : InputIdx}
    (valid : var.validIn aig) (eq : aig.get var valid = .input idx) :
    idx.getVar aig = var := by
  grind

grind_pattern input_getVar_get => idx.getVar aig, Node.input idx, aig.get var valid

/--
All latch indices point to a latch in the Aig.
-/
@[expose, local grind, local simp]
def LatchesValid (aig : Aig) : Prop :=
  ∀ {idx : LatchIdx} (valid : idx.validIn aig),
  ∃ (valid' : (idx.getVar aig valid).validIn aig),
    aig.get (idx.getVar aig valid) = .latch idx

@[simp]
theorem latch_getVar_validIn {latchesValid : aig.LatchesValid} {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getVar aig valid |>.validIn aig := by
  grind

grind_pattern latch_getVar_validIn => idx.getVar aig valid |>.validIn aig

@[simp]
theorem get_latch_getVar {latchesValid : aig.LatchesValid} {idx : LatchIdx} (valid : idx.validIn aig) :
    aig.get (idx.getVar aig valid) = .latch idx := by
  grind

grind_pattern get_latch_getVar => aig.get (idx.getVar aig valid)

/-
Equivalent theorem on leaves
-/
@[simp]
theorem leaf_getVar_validIn {inputsValid : aig.InputsValid} {latchesValid : aig.LatchesValid}
    {idx : LeafIdx} (valid : idx.validIn aig) :
    idx.getVar aig valid |>.validIn aig := by
  grind

grind_pattern leaf_getVar_validIn => idx.getVar aig valid |>.validIn aig

/--
All latches in the Aig point to a corresponding latch index.
-/
@[expose, local grind, local simp]
def LatchIdxsValid (aig : Aig) : Prop :=
  ∀ {var : Var} (valid : var.validIn aig),
  match aig.get var valid with
  | .latch idx =>
    ∃ (valid' : idx.validIn aig), idx.getVar aig valid' = var
  | _ => true

@[simp]
theorem validIn_of_get_eq_latch {latchIdxsValid : aig.LatchIdxsValid} {var : Var} {idx : LatchIdx}
    (valid : var.validIn aig) (eq : aig.get var valid = .latch idx) :
    idx.validIn aig := by
  grind

grind_pattern validIn_of_get_eq_latch => idx.validIn aig, Node.latch idx, aig.get var valid

@[simp]
theorem latch_getVar_get {latchIdxsValid : aig.LatchIdxsValid} {var : Var} {idx : LatchIdx}
    (valid : var.validIn aig) (eq : aig.get var valid = .latch idx) :
    idx.getVar aig = var := by
  grind

grind_pattern latch_getVar_get => idx.getVar aig, Node.latch idx, aig.get var valid

/--
All latch reset literals are valid in the Aig.
This follows from `LatchesValid` and `AcyclicResets`.
-/
@[expose, local grind, local simp]
def ResetsValid (aig : Aig) : Prop :=
  ∀ {idx : LatchIdx} (valid : idx.validIn aig),
    (idx.getReset aig valid).validIn aig

@[simp]
theorem getReset_validIn {resetsValid : aig.ResetsValid} {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getReset aig valid |>.validIn aig := by
  grind

grind_pattern getReset_validIn => idx.getReset aig valid |>.validIn aig

/--
All latch next state literals are valid in the Aig.
-/
@[expose, local grind, local simp]
def NextsValid (aig : Aig) : Prop :=
  ∀ {idx : LatchIdx} (valid : idx.validIn aig),
    (idx.getNext aig valid).validIn aig

@[simp]
theorem getNext_validIn {nextsValid : aig.NextsValid} {idx : LatchIdx} (valid : idx.validIn aig) :
    idx.getNext aig valid |>.validIn aig := by
  grind

grind_pattern getNext_validIn => idx.getNext aig valid |>.validIn aig

/--
The gates of the Aig are acyclic.
This is enforced by requiring each gate's inputs to have lower variable
indices than themselves.
-/
@[expose, local grind, local simp]
def AcyclicGates (aig : Aig) : Prop :=
  ∀ {var : Var} {rhs0 rhs1} (valid : var.validIn aig),
    aig.get var valid = .and rhs0 rhs1 → rhs0.var < var ∧ rhs1.var < var

@[simp]
theorem rhs0_lt_of_get_eq_and {acyclicGates : aig.AcyclicGates} {var : Var} {rhs0 rhs1 : Lit}
    (valid : var.validIn aig) (eq : aig.get var valid = .and rhs0 rhs1) :
    rhs0.var < var := by
  grind

@[simp]
theorem rhs1_lt_of_get_eq_and {acyclicGates : aig.AcyclicGates} {var : Var} {rhs0 rhs1 : Lit}
    (valid : var.validIn aig) (eq : aig.get var valid = .and rhs0 rhs1) :
    rhs1.var < var := by
  grind

theorem rhs0_lt_of_get_eq_and_lt {acyclicGates : aig.AcyclicGates} {var var' : Var} {rhs0 rhs1 : Lit}
    (valid : var.validIn aig) (eq : aig.get var valid = .and rhs0 rhs1) (lt : var ≤ var') :
    rhs0.var < var' := by
  grind

grind_pattern rhs0_lt_of_get_eq_and_lt => rhs0.var < var', Node.and rhs0 rhs1, aig.get var valid
grind_pattern rhs0_lt_of_get_eq_and_lt => rhs0.var ≤ var', Node.and rhs0 rhs1, aig.get var valid

theorem rhs1_lt_of_get_eq_and_lt {acyclicGates : aig.AcyclicGates} {var var' : Var} {rhs0 rhs1 : Lit}
    (valid : var.validIn aig) (eq : aig.get var valid = .and rhs0 rhs1) (lt : var ≤ var') :
    rhs1.var < var' := by
  grind

grind_pattern rhs1_lt_of_get_eq_and_lt => rhs1.var < var', Node.and rhs0 rhs1, aig.get var valid
grind_pattern rhs1_lt_of_get_eq_and_lt => rhs1.var ≤ var', Node.and rhs0 rhs1, aig.get var valid

/--
The reset function of the Aig is acyclic.
This is enfoced by requiring each latch's reset to have a lower variable
index than the latch's output.
-/
@[expose, local grind, local simp]
def AcyclicResets (aig : Aig) : Prop :=
  ∀ {idx : LatchIdx} (valid : idx.validIn aig),
    (idx.getReset aig valid).var < idx.getVar aig valid

theorem ResetsValid_of_LatchesValid_AcyclicReset {aig : Aig}
    (latchesValid : aig.LatchesValid)
    (acyclicResets : aig.AcyclicResets) :
    aig.ResetsValid := by
  grind

@[simp]
theorem getReset_lt_getVar (acyclicResets : aig.AcyclicResets) {idx : LatchIdx} (valid : idx.validIn aig) :
    (idx.getReset aig valid).var < idx.getVar aig valid := by
  grind

theorem getReset_lt_getVar_of_lt (acyclicResets : aig.AcyclicResets) {var : Var} {idx : LatchIdx}
    (valid : idx.validIn aig) (lt : idx.getVar aig valid ≤ var) :
    (idx.getReset aig valid).var < var := by
  grind

grind_pattern getReset_lt_getVar_of_lt => (idx.getReset aig valid).var < var
grind_pattern getReset_lt_getVar_of_lt => (idx.getReset aig valid).var ≤ var

/--
All indices within the Aig are valid and the gates and reset function are
acyclic, allowing the definition of semantics
-/
@[local grind]
structure WellFormed (aig : Aig) : Prop where
  inputsValid : aig.InputsValid
  inputIdxsValid : aig.InputIdxsValid

  latchesValid : aig.LatchesValid
  latchIdxsValid : aig.LatchIdxsValid
  resetsValid : aig.ResetsValid
  nextsValid : aig.NextsValid

  acyclicGates : aig.AcyclicGates
  acyclicResets : aig.AcyclicResets

section triggers

theorem InputsValid_of_WellFormed (wf : aig.WellFormed) : aig.InputsValid := wf.inputsValid
grind_pattern InputsValid_of_WellFormed => aig.WellFormed, aig.InputsValid

theorem InputIdxsValid_of_WellFormed (wf : aig.WellFormed) : aig.InputIdxsValid := wf.inputIdxsValid
grind_pattern InputIdxsValid_of_WellFormed => aig.WellFormed, aig.InputIdxsValid

theorem LatchesValid_of_WellFormed (wf : aig.WellFormed) : aig.LatchesValid := wf.latchesValid
grind_pattern LatchesValid_of_WellFormed => aig.WellFormed, aig.LatchesValid

theorem LatchIdxsValid_of_WellFormed (wf : aig.WellFormed) : aig.LatchIdxsValid := wf.latchIdxsValid
grind_pattern LatchIdxsValid_of_WellFormed => aig.WellFormed, aig.LatchIdxsValid

theorem ResetsValid_of_WellFormed (wf : aig.WellFormed) : aig.ResetsValid := wf.resetsValid
grind_pattern ResetsValid_of_WellFormed => aig.WellFormed, aig.ResetsValid

theorem NextsValid_of_WellFormed (wf : aig.WellFormed) : aig.NextsValid := wf.nextsValid
grind_pattern NextsValid_of_WellFormed => aig.WellFormed, aig.NextsValid

theorem AcyclicGates_of_WellFormed (wf : aig.WellFormed) : aig.AcyclicGates := wf.acyclicGates
grind_pattern AcyclicGates_of_WellFormed => aig.WellFormed, aig.AcyclicGates

theorem AcyclicResets_of_WellFormed (wf : aig.WellFormed) : aig.AcyclicResets := wf.acyclicResets
grind_pattern AcyclicResets_of_WellFormed => aig.WellFormed, aig.AcyclicResets

end triggers

/-
We consider the same patterns for invariant preservation as in the case of the get/set lemmas
-/

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
theorem WellFormed_addAnd
    (idxsValid : aig.WellFormed)
    (h0 : rhs0.validIn aig)
    (h1 : rhs1.validIn aig) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.WellFormed := by
  grind

grind_pattern WellFormed_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst.WellFormed

end addAnd
