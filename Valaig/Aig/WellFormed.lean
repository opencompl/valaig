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
theorem validIn_of_get_input {inputIdxsValid : aig.InputIdxsValid} {var : Var} {idx : InputIdx}
    (valid : var.validIn aig) (eq : aig.get var valid = .input idx) :
    idx.validIn aig := by
  grind

grind_pattern validIn_of_get_input => idx.validIn aig, Node.input idx, aig.get var valid

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
theorem validIn_of_get_latch {latchIdxsValid : aig.LatchIdxsValid} {var : Var} {idx : LatchIdx}
    (valid : var.validIn aig) (eq : aig.get var valid = .latch idx) :
    idx.validIn aig := by
  grind

grind_pattern validIn_of_get_latch => idx.validIn aig, Node.latch idx, aig.get var valid

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
    match idx.getReset aig valid with
    | none => True
    | some lit => lit.validIn aig

@[simp]
theorem getReset_validIn {resetsValid : aig.ResetsValid} {idx : LatchIdx} (valid : idx.validIn aig)
    {lit : Lit} (isSome : idx.getReset aig valid = some lit) :
    lit.validIn aig := by
  grind

grind_pattern getReset_validIn => idx.getReset aig valid, some lit, lit.validIn aig

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

section AcyclicGates
variable {acyclicGates : aig.AcyclicGates} {var var' : Var} {rhs0 rhs1 : Lit}
variable (valid : var.validIn aig) (eq : aig.get var valid = .and rhs0 rhs1)
include acyclicGates valid eq

@[simp]
theorem rhs0_lt_of_get_and :
    rhs0.var < var := by
  grind

@[simp]
theorem rhs1_lt_of_get_and :
    rhs1.var < var := by
  grind

theorem rhs0_lt_of_get_and_lt (lt : var ≤ var') :
    rhs0.var < var' := by
  grind

grind_pattern rhs0_lt_of_get_and_lt => rhs0.var < var', Node.and rhs0 rhs1, aig.get var valid
grind_pattern rhs0_lt_of_get_and_lt => rhs0.var ≤ var', Node.and rhs0 rhs1, aig.get var valid

theorem rhs1_lt_of_get_and_lt (lt : var ≤ var') :
    rhs1.var < var' := by
  grind

grind_pattern rhs1_lt_of_get_and_lt => rhs1.var < var', Node.and rhs0 rhs1, aig.get var valid
grind_pattern rhs1_lt_of_get_and_lt => rhs1.var ≤ var', Node.and rhs0 rhs1, aig.get var valid

@[simp]
theorem rhs0_validIn_of_get_and :
    rhs0.var.validIn aig := by
  grind

grind_pattern rhs0_validIn_of_get_and => rhs0.var.validIn aig, Node.and rhs0 rhs1, aig.get var valid

@[simp]
theorem rhs1_validIn_of_get_and :
    rhs1.var.validIn aig := by
  grind

grind_pattern rhs1_validIn_of_get_and => rhs1.var.validIn aig, Node.and rhs0 rhs1, aig.get var valid

end AcyclicGates

/--
The reset function of the Aig is acyclic.
This is enfoced by requiring each latch's reset to have a lower variable
index than the latch's output.
-/
@[expose, local grind, local simp]
def AcyclicResets (aig : Aig) : Prop :=
  ∀ {idx : LatchIdx} (valid : idx.validIn aig),
    match idx.getReset aig valid with
    | none => True
    | some lit => lit.var < idx.getVar aig valid

theorem ResetsValid_of_LatchesValid_AcyclicReset {aig : Aig}
    (latchesValid : aig.LatchesValid)
    (acyclicResets : aig.AcyclicResets) :
    aig.ResetsValid := by
  grind

@[simp]
theorem getReset_lt_getVar (acyclicResets : aig.AcyclicResets) {idx : LatchIdx} (valid : idx.validIn aig)
    {lit : Lit} (isSome : idx.getReset aig valid = some lit) :
    lit.var < idx.getVar aig valid := by
  grind

theorem getReset_lt_getVar_of_lt (acyclicResets : aig.AcyclicResets) {var : Var} {idx : LatchIdx}
    (valid : idx.validIn aig) (lt : idx.getVar aig valid ≤ var)
    {lit : Lit} (isSome : idx.getReset aig valid = some lit) :
    lit.var < var := by
  grind

grind_pattern getReset_lt_getVar_of_lt => idx.getReset aig valid, some lit, lit.var < var
grind_pattern getReset_lt_getVar_of_lt => idx.getReset aig valid, some lit, lit.var ≤ var

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
variable (wf : aig.WellFormed)
include wf

theorem InputsValid_of_WellFormed    : aig.InputsValid    := wf.inputsValid
theorem InputIdxsValid_of_WellFormed : aig.InputIdxsValid := wf.inputIdxsValid
theorem LatchesValid_of_WellFormed   : aig.LatchesValid   := wf.latchesValid
theorem LatchIdxsValid_of_WellFormed : aig.LatchIdxsValid := wf.latchIdxsValid
theorem ResetsValid_of_WellFormed    : aig.ResetsValid    := wf.resetsValid
theorem NextsValid_of_WellFormed     : aig.NextsValid     := wf.nextsValid
theorem AcyclicGates_of_WellFormed   : aig.AcyclicGates   := wf.acyclicGates
theorem AcyclicResets_of_WellFormed  : aig.AcyclicResets  := wf.acyclicResets

grind_pattern AcyclicResets_of_WellFormed  => aig.WellFormed, aig.AcyclicResets
grind_pattern AcyclicGates_of_WellFormed   => aig.WellFormed, aig.AcyclicGates
grind_pattern InputsValid_of_WellFormed    => aig.WellFormed, aig.InputsValid
grind_pattern InputIdxsValid_of_WellFormed => aig.WellFormed, aig.InputIdxsValid
grind_pattern LatchesValid_of_WellFormed   => aig.WellFormed, aig.LatchesValid
grind_pattern LatchIdxsValid_of_WellFormed => aig.WellFormed, aig.LatchIdxsValid
grind_pattern ResetsValid_of_WellFormed    => aig.WellFormed, aig.ResetsValid
grind_pattern NextsValid_of_WellFormed     => aig.WellFormed, aig.NextsValid

end triggers

/-
We consider the same patterns for invariant preservation as in the case of the get/set lemmas
-/

/-
Aig.empty Lemmas.
-/
section empty

@[simp] theorem InputsValid_empty    : empty.InputsValid    := by grind
@[simp] theorem InputIdxsValid_empty : empty.InputIdxsValid := by grind
@[simp] theorem LatchesValid_empty   : empty.LatchesValid   := by grind
@[simp] theorem LatchIdxsValid_empty : empty.LatchIdxsValid := by grind
@[simp] theorem ResetsValid_empty    : empty.ResetsValid    := by grind
@[simp] theorem NextsValid_empty     : empty.NextsValid     := by grind
@[simp] theorem AcyclicGates_empty   : empty.AcyclicGates   := by grind
@[simp] theorem AcyclicResets_empty  : empty.AcyclicResets  := by grind

grind_pattern InputsValid_empty    => empty.InputsValid
grind_pattern InputIdxsValid_empty => empty.InputIdxsValid
grind_pattern LatchesValid_empty   => empty.LatchesValid
grind_pattern LatchIdxsValid_empty => empty.LatchIdxsValid
grind_pattern ResetsValid_empty    => empty.ResetsValid
grind_pattern NextsValid_empty     => empty.NextsValid
grind_pattern AcyclicGates_empty   => empty.AcyclicGates
grind_pattern AcyclicResets_empty  => empty.AcyclicResets

@[simp] theorem WellFormed_empty : empty.WellFormed := by grind
grind_pattern WellFormed_empty => empty.WellFormed

end empty

/-
LatchIdx.setNext Lemmas.
-/
section setNext
variable {setIdx : LatchIdx} {newNext : Lit}

@[simp]
theorem InputsValid_setNext
    (inputsValid : aig.InputsValid) :
    (setIdx.setNext aig newNext).InputsValid := by
  grind

@[simp]
theorem InputIdxsValid_setNext
    (inputIdxsValid : aig.InputIdxsValid) :
    (setIdx.setNext aig newNext).InputIdxsValid := by
  grind

@[simp]
theorem LatchesValid_setNext
    (latchesValid : aig.LatchesValid) :
    (setIdx.setNext aig newNext).LatchesValid := by
  grind

@[simp]
theorem LatchIdxsValid_setNext
    (latchIdxsValid : aig.LatchIdxsValid) :
    (setIdx.setNext aig newNext).LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_setNext
    (resetsValid : aig.ResetsValid) :
    (setIdx.setNext aig newNext).ResetsValid := by
  grind

@[simp]
theorem NextsValid_setNext
    (nextsValid : aig.NextsValid)
    (nextValid : newNext.validIn aig) :
    (setIdx.setNext aig newNext).NextsValid := by
  grind

@[simp]
theorem AcyclicGates_setNext
    (acyclicGates : aig.AcyclicGates) :
    (setIdx.setNext aig newNext).AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_setNext
    (acyclicResets : aig.AcyclicResets) :
    (setIdx.setNext aig newNext).AcyclicResets := by
  grind

-- TODO: These grind patterns could be created with @[grind .], but this seems
-- to spend a lot of compilation time working out the pattern, by doing it
-- manually we avoid this
grind_pattern InputsValid_setNext    => (setIdx.setNext aig newNext).InputsValid
grind_pattern InputIdxsValid_setNext => (setIdx.setNext aig newNext).InputIdxsValid
grind_pattern LatchesValid_setNext   => (setIdx.setNext aig newNext).LatchesValid
grind_pattern LatchIdxsValid_setNext => (setIdx.setNext aig newNext).LatchIdxsValid
grind_pattern ResetsValid_setNext    => (setIdx.setNext aig newNext).ResetsValid
grind_pattern NextsValid_setNext     => (setIdx.setNext aig newNext).NextsValid
grind_pattern AcyclicGates_setNext   => (setIdx.setNext aig newNext).AcyclicGates
grind_pattern AcyclicResets_setNext  => (setIdx.setNext aig newNext).AcyclicResets

@[simp]
theorem WellFormed_setNext
    (wellFormed : aig.WellFormed)
    (nextValid : newNext.validIn aig) :
    (setIdx.setNext aig newNext).WellFormed := by
  grind

grind_pattern WellFormed_setNext => (setIdx.setNext aig newNext).WellFormed

end setNext

/-
LatchIdx.setReset Lemmas.
-/
section setReset
variable {setIdx : LatchIdx} {newReset : Option Lit}

@[simp]
theorem InputsValid_setReset
    (inputsValid : aig.InputsValid) :
    (setIdx.setReset aig newReset).InputsValid := by
  grind

@[simp]
theorem InputIdxsValid_setReset
    (inputIdxsValid : aig.InputIdxsValid) :
    (setIdx.setReset aig newReset).InputIdxsValid := by
  grind

@[simp]
theorem LatchesValid_setReset
    (latchesValid : aig.LatchesValid) :
    (setIdx.setReset aig newReset).LatchesValid := by
  grind

@[simp]
theorem LatchIdxsValid_setReset
    (latchIdxsValid : aig.LatchIdxsValid) :
    (setIdx.setReset aig newReset).LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_setReset_none
    (resetsValid : aig.ResetsValid) :
    (setIdx.setReset aig none).ResetsValid := by
  grind

@[simp]
theorem ResetsValid_of_resetValid_setReset_some
    (resetsValid : aig.ResetsValid)
    {newReset : Lit}
    (resetValid : newReset.validIn aig) :
    (setIdx.setReset aig <| some newReset).ResetsValid := by
  grind

theorem ResetsValid_of_resetValid_setReset
    (resetsValid : aig.ResetsValid)
    (resetValid :
      match newReset with
      | none => True
      | some lit => lit.validIn aig) :
    (setIdx.setReset aig newReset).ResetsValid := by
  grind

@[simp]
theorem ResetsValid_setReset_some
    (resetsValid : aig.ResetsValid)
    {newReset : Lit}
    (resetValid : newReset.var < setIdx.getVar aig setValid)
    (varValid : (setIdx.getVar aig setValid).validIn aig) :
    (setIdx.setReset aig <| some newReset).ResetsValid := by
  grind

theorem ResetsValid_setReset
    (resetsValid : aig.ResetsValid)
    (resetValid :
      match newReset with
      | none => True
      | some lit => lit.var < setIdx.getVar aig setValid)
    (varValid : (setIdx.getVar aig setValid).validIn aig) :
    (setIdx.setReset aig newReset).ResetsValid := by
  grind

@[simp]
theorem NextsValid_setReset
    (nextsValid : aig.NextsValid) :
    (setIdx.setReset aig newReset).NextsValid := by
  grind

@[simp]
theorem AcyclicGates_setReset
    (acyclicGates : aig.AcyclicGates) :
    (setIdx.setReset aig newReset).AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_setReset_none
    (acyclicResets : aig.AcyclicResets) :
    (setIdx.setReset aig none).AcyclicResets := by
  grind

@[simp]
theorem AcyclicResets_setReset_some
    (acyclicResets : aig.AcyclicResets)
    {newReset : Lit}
    (resetValid : newReset.var < setIdx.getVar aig setValid) :
    (setIdx.setReset aig <| some newReset).AcyclicResets := by
  grind

theorem AcyclicResets_setReset
    (acyclicResets : aig.AcyclicResets)
    (resetValid :
      match newReset with
      | none => True
      | some lit => lit.var < setIdx.getVar aig setValid) :
    (setIdx.setReset aig newReset).AcyclicResets := by
  grind

grind_pattern InputsValid_setReset    => (setIdx.setReset aig newReset).InputsValid
grind_pattern InputIdxsValid_setReset => (setIdx.setReset aig newReset).InputIdxsValid
grind_pattern LatchesValid_setReset   => (setIdx.setReset aig newReset).LatchesValid
grind_pattern LatchIdxsValid_setReset => (setIdx.setReset aig newReset).LatchIdxsValid
grind_pattern ResetsValid_setReset    => (setIdx.setReset aig newReset).ResetsValid
grind_pattern NextsValid_setReset     => (setIdx.setReset aig newReset).NextsValid
grind_pattern AcyclicGates_setReset   => (setIdx.setReset aig newReset).AcyclicGates
grind_pattern AcyclicResets_setReset  => (setIdx.setReset aig newReset).AcyclicResets

@[simp]
theorem WellFormed_setReset_none
    (wellFormed : aig.WellFormed) :
    (setIdx.setReset aig none).WellFormed := by
  grind

@[simp]
theorem WellFormed_setReset_some
    (wellFormed : aig.WellFormed)
    {newReset : Lit}
    (resetValid : newReset.var < setIdx.getVar aig setValid) :
    (setIdx.setReset aig <| some newReset ).WellFormed := by
  grind

theorem WellFormed_setReset
    (wellFormed : aig.WellFormed)
    (resetValid :
      match newReset with
      | none => True
      | some lit => lit.var < setIdx.getVar aig setValid) :
    (setIdx.setReset aig newReset).WellFormed := by
  grind

grind_pattern WellFormed_setReset => (setIdx.setReset aig newReset).WellFormed

end setReset

/-
Aig.addInput' Lemmas.
-/
section addInput'
variable {idx : InputIdx}

-- TODO: These/monotone assume the index isn't overlapping, but it would be good to still be able
-- to reason about what happens even when that is broken

@[simp]
theorem InputsValid_addInput'
    (inputsValid : aig.InputsValid)
    (h : ¬idx.validIn aig) :
    (aig.addInput' idx).InputsValid := by
  grind

@[simp]
theorem InputIdxsValid_addInput'
    (inputIdxsValid : aig.InputIdxsValid)
    (h : ¬idx.validIn aig) :
    (aig.addInput' idx).InputIdxsValid := by
  grind

@[simp]
theorem LatchesValid_addInput'
    (latchesValid : aig.LatchesValid)
    (h : ¬idx.validIn aig) :
    (aig.addInput' idx).LatchesValid := by
  grind

@[simp]
theorem LatchIdxsValid_addInput'
    (latchIdxsValid : aig.LatchIdxsValid)
    (h : ¬idx.validIn aig) :
    (aig.addInput' idx).LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_addInput'
    (resetsValid : aig.ResetsValid)
    (h : ¬idx.validIn aig) :
    (aig.addInput' idx).ResetsValid := by
  grind

@[simp]
theorem NextsValid_addInput'
    (nextsValid : aig.NextsValid)
    (h : ¬idx.validIn aig) :
    (aig.addInput' idx).NextsValid := by
  grind

@[simp]
theorem AcyclicGates_addInput'
    (acyclicGates : aig.AcyclicGates)
    (h : ¬idx.validIn aig) :
    (aig.addInput' idx).AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_addInput'
    (acyclicResets : aig.AcyclicResets)
    (h : ¬idx.validIn aig) :
    (aig.addInput' idx).AcyclicResets := by
  grind

grind_pattern InputsValid_addInput'    => (aig.addInput' idx).InputsValid
grind_pattern InputIdxsValid_addInput' => (aig.addInput' idx).InputIdxsValid
grind_pattern LatchesValid_addInput'   => (aig.addInput' idx).LatchesValid
grind_pattern LatchIdxsValid_addInput' => (aig.addInput' idx).LatchIdxsValid
grind_pattern ResetsValid_addInput'    => (aig.addInput' idx).ResetsValid
grind_pattern NextsValid_addInput'     => (aig.addInput' idx).NextsValid
grind_pattern AcyclicGates_addInput'   => (aig.addInput' idx).AcyclicGates
grind_pattern AcyclicResets_addInput'  => (aig.addInput' idx).AcyclicResets

@[simp]
theorem WellFormed_addInput'
    (wellFormed : aig.WellFormed)
    (h : ¬idx.validIn aig) :
    (aig.addInput' idx).WellFormed := by
  grind

grind_pattern WellFormed_addInput' => (aig.addInput' idx).WellFormed

end addInput'

/-
Aig.addLatch' Lemmas.
-/
section addLatch'
variable {idx : LatchIdx} {next : Lit} {reset : Option Lit}

@[simp]
theorem InputsValid_addLatch'
    (inputsValid : aig.InputsValid)
    (h : ¬idx.validIn aig) :
    (aig.addLatch' idx next reset).InputsValid := by
  grind

@[simp]
theorem InputIdxsValid_addLatch'
    (inputIdxsValid : aig.InputIdxsValid)
    (h : ¬idx.validIn aig) :
    (aig.addLatch' idx next reset).InputIdxsValid := by
  grind

@[simp]
theorem LatchesValid_addLatch'
    (latchesValid : aig.LatchesValid)
    (h : ¬idx.validIn aig) :
    (aig.addLatch' idx next reset).LatchesValid := by
  grind

@[simp]
theorem LatchIdxsValid_addLatch'
    (latchIdxsValid : aig.LatchIdxsValid)
    (h : ¬idx.validIn aig) :
    (aig.addLatch' idx next reset).LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_addLatch'_none
    (resetsValid : aig.ResetsValid)
    (h : ¬idx.validIn aig) :
    (aig.addLatch' idx next none).ResetsValid := by
  grind

@[simp]
theorem ResetsValid_addLatch'_some
    (resetsValid : aig.ResetsValid)
    (h : ¬idx.validIn aig)
    {reset : Lit}
    (resetValid : reset.validIn aig) :
    (aig.addLatch' idx next <| some reset).ResetsValid := by
  grind

theorem ResetsValid_addLatch'
    (resetsValid : aig.ResetsValid)
    (h : ¬idx.validIn aig)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.validIn aig) :
    (aig.addLatch' idx next reset).ResetsValid := by
  grind

@[simp]
theorem NextsValid_addLatch'
    (nextsValid : aig.NextsValid)
    (h : ¬idx.validIn aig)
    (nextValid : next.validIn aig) :
    (aig.addLatch' idx next reset).NextsValid := by
  grind

@[simp]
theorem AcyclicGates_addLatch'
    (acyclicGates : aig.AcyclicGates)
    (h : ¬idx.validIn aig) :
    (aig.addLatch' idx next reset).AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_addLatch'_none
    (acyclicResets : aig.AcyclicResets)
    (h : ¬idx.validIn aig) :
    (aig.addLatch' idx next none).AcyclicResets := by
  grind

@[simp]
theorem AcyclicResets_addLatch'_some
    (acyclicResets : aig.AcyclicResets)
    (h : ¬idx.validIn aig)
    {reset : Lit}
    (resetValid : reset.validIn aig) :
    (aig.addLatch' idx next <| some reset).AcyclicResets := by
  grind

theorem AcyclicResets_addLatch'
    (acyclicResets : aig.AcyclicResets)
    (h : ¬idx.validIn aig)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.validIn aig) :
    (aig.addLatch' idx next reset).AcyclicResets := by
  grind

grind_pattern InputsValid_addLatch'    => (aig.addLatch' idx next reset).InputsValid
grind_pattern InputIdxsValid_addLatch' => (aig.addLatch' idx next reset).InputIdxsValid
grind_pattern LatchesValid_addLatch'   => (aig.addLatch' idx next reset).LatchesValid
grind_pattern LatchIdxsValid_addLatch' => (aig.addLatch' idx next reset).LatchIdxsValid
grind_pattern ResetsValid_addLatch'    => (aig.addLatch' idx next reset).ResetsValid
grind_pattern NextsValid_addLatch'     => (aig.addLatch' idx next reset).NextsValid
grind_pattern AcyclicGates_addLatch'   => (aig.addLatch' idx next reset).AcyclicGates
grind_pattern AcyclicResets_addLatch'  => (aig.addLatch' idx next reset).AcyclicResets

@[simp]
theorem WellFormed_addLatch'_none
    (wellFormed : aig.WellFormed)
    (h : ¬idx.validIn aig)
    (nextValid : next.validIn aig) :
    (aig.addLatch' idx next none).WellFormed := by
  grind

@[simp]
theorem WellFormed_addLatch'_some
    (wellFormed : aig.WellFormed)
    (h : ¬idx.validIn aig)
    (nextValid : next.validIn aig)
    {reset : Lit}
    (resetValid : reset.validIn aig) :
    (aig.addLatch' idx next <| some reset).WellFormed := by
  grind

theorem WellFormed_addLatch'
    (wellFormed : aig.WellFormed)
    (h : ¬idx.validIn aig)
    (nextValid : next.validIn aig)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.validIn aig) :
    (aig.addLatch' idx next reset).WellFormed := by
  grind

grind_pattern WellFormed_addLatch' => (aig.addLatch' idx next reset).WellFormed

end addLatch'

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

grind_pattern InputsValid_addAnd    => (aig.addAnd rhs0 rhs1 h0 h1).fst.InputsValid
grind_pattern InputIdxsValid_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst.InputIdxsValid
grind_pattern LatchesValid_addAnd   => (aig.addAnd rhs0 rhs1 h0 h1).fst.LatchesValid
grind_pattern LatchIdxsValid_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst.LatchIdxsValid
grind_pattern ResetsValid_addAnd    => (aig.addAnd rhs0 rhs1 h0 h1).fst.ResetsValid
grind_pattern NextsValid_addAnd     => (aig.addAnd rhs0 rhs1 h0 h1).fst.NextsValid
grind_pattern AcyclicGates_addAnd   => (aig.addAnd rhs0 rhs1 h0 h1).fst.AcyclicGates
grind_pattern AcyclicResets_addAnd  => (aig.addAnd rhs0 rhs1 h0 h1).fst.AcyclicResets

@[simp]
theorem WellFormed_addAnd
    (wellFormed : aig.WellFormed)
    (h0 : rhs0.validIn aig)
    (h1 : rhs1.validIn aig) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.WellFormed := by
  grind

grind_pattern WellFormed_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst.WellFormed

end addAnd
