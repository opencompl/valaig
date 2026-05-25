module

public import Valaig.Aig.Lemmas.Basic
import Valaig.Aig.Lemmas.Modify
import all Valaig.Aig.Lemmas.Modify
import Valaig.Aig.Lemmas.Monotone

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
  ∀ idx (_ : idx ∈ aig.inputs),
  ∃ (_ : aig.inputs[idx].var ∈ aig.nodes),
    aig.nodes[aig.inputs[idx].var] = idx

@[simp, grind .]
theorem WF.var_inputs_mem_nodes {inputsValid : aig.InputsValid} {idx : InputIdx} (mem : idx ∈ aig.inputs) :
    (aig.inputs[idx]'mem).var ∈ aig.nodes := by
  grind

@[simp, grind =]
theorem WF.nodes_var_inputs_eq {inputsValid : aig.InputsValid} {idx : InputIdx} (mem : idx ∈ aig.inputs) :
    aig.nodes[(aig.inputs[idx]'mem).var] = idx := by
  grind

/--
  All inputs in the Aig point to a corresponding input index.
-/
@[expose, local grind, local simp]
def InputIdxsValid (aig : Aig) : Prop :=
  ∀ var (_ : var ∈ aig.nodes) idx,
    aig[var] = .input idx → ∃ _, aig.inputs[idx].var = var

@[simp]
theorem WF.mem_inputs_of_node {inputIdxsValid : aig.InputIdxsValid} {var : Var} {idx : InputIdx}
    (mem : var ∈ aig.nodes) (eq : aig[var] = .input idx) :
    idx ∈ aig.inputs := by
  grind

grind_pattern WF.mem_inputs_of_node => idx ∈ aig.inputs, aig[var], Node.input idx

@[simp]
theorem WF.var_inputs_of_node {inputIdxsValid : aig.InputIdxsValid} {var : Var} {idx : InputIdx}
    (mem : var ∈ aig.nodes) (eq : aig[var] = .input idx) :
    aig.inputs[idx].var = var := by
  grind

grind_pattern WF.var_inputs_of_node => idx ∈ aig.inputs, aig[var], Node.input idx

/--
  All latch indices point to a latch in the Aig.
-/
@[expose, local grind, local simp]
def LatchesValid (aig : Aig) : Prop :=
  ∀ idx (_ : idx ∈ aig.latches),
  ∃ (_ : aig.latches[idx].var ∈ aig.nodes),
    aig.nodes[aig.latches[idx].var] = idx

@[simp, grind .]
theorem WF.var_latches_mem_nodes {latchesValid : aig.LatchesValid} {idx : LatchIdx} (mem : idx ∈ aig.latches) :
    (aig.latches[idx]'mem).var ∈ aig.nodes := by
  grind

@[simp, grind =]
theorem WF.nodes_var_latches_eq {latchesValid : aig.LatchesValid} {idx : LatchIdx} (mem : idx ∈ aig.latches) :
    aig.nodes[(aig.latches[idx]'mem).var] = idx := by
  grind

/--
  All latches in the Aig point to a corresponding latch index.
-/
@[expose, local grind, local simp]
def LatchIdxsValid (aig : Aig) : Prop :=
  ∀ var (_ : var ∈ aig.nodes) idx,
    aig[var] = .latch idx → ∃ _, aig.latches[idx].var = var

@[simp]
theorem WF.mem_latches_of_node {latchIdxsValid : aig.LatchIdxsValid} {var : Var} {idx : LatchIdx}
    (mem : var ∈ aig.nodes) (eq : aig[var] = .latch idx) :
    idx ∈ aig.latches := by
  grind

grind_pattern WF.mem_latches_of_node => idx ∈ aig.latches, aig[var], Node.latch idx

@[simp]
theorem WF.var_latches_of_node {latchIdxsValid : aig.LatchIdxsValid} {var : Var} {idx : LatchIdx}
    (mem : var ∈ aig.nodes) (eq : aig[var] = .latch idx) :
    aig.latches[idx].var = var := by
  grind

grind_pattern WF.var_latches_of_node => idx ∈ aig.latches, aig[var], Node.latch idx

/-
  Equivalent of `getElem_nodes_LatchesValid` on leaves.
-/
@[simp]
theorem WF.getVar_LeafIdxsValid {inputsValid : aig.InputsValid} {latchesValid : aig.LatchesValid}
    {idx : LeafIdx} (valid : idx.validIn aig) :
    idx.getVar aig valid ∈ aig.nodes := by
  grind

grind_pattern WF.getVar_LeafIdxsValid => idx.getVar aig valid ∈ aig.nodes

/--
  All latch reset literals are valid in the Aig.
  This follows from `LatchesValid` and `AcyclicResets`.
-/
@[expose, local grind, local simp]
def ResetsValid (aig : Aig) : Prop :=
  ∀ idx (_ : idx ∈ aig.latches),
    match aig.latches[idx].reset with
    | none => True
    | some lit => lit.validIn aig

@[simp]
theorem WF.mem_nodes_reset {resetsValid : aig.ResetsValid} {idx : LatchIdx} (mem : idx ∈ aig.latches)
    {lit : Lit} (isSome : aig.latches[idx].reset = some lit) :
    lit.validIn aig := by
  grind

grind_pattern WF.mem_nodes_reset => aig.latches[idx].reset, some lit, lit.validIn aig

/--
  All latch next state literals are valid in the Aig.
-/
@[expose, local grind, local simp]
def NextsValid (aig : Aig) : Prop :=
  ∀ idx (_ : idx ∈ aig.latches),
    aig.latches[idx].next.validIn aig

@[simp, grind .]
theorem WF.mem_nodes_next {nextsValid : aig.NextsValid} {idx : LatchIdx} (mem : idx ∈ aig.latches) :
    aig.latches[idx].next.validIn aig := by
  grind

/--
  The gates of the Aig are acyclic.
  This is enforced by requiring each gate's inputs to have lower variable
  indices than themselves.
-/
@[expose, local grind, local simp]
def AcyclicGates (aig : Aig) : Prop :=
  ∀ {var : Var} {rhs0 rhs1} (mem : var ∈ aig.nodes),
    aig.nodes[var] = .and rhs0 rhs1 → rhs0.var < var ∧ rhs1.var < var

section AcyclicGates
variable {acyclicGates : aig.AcyclicGates} {var var' : Var} {rhs0 rhs1 : Lit}
variable (valid : var.validIn aig) (eq : aig.nodes[var] = .and rhs0 rhs1)
include acyclicGates valid eq

@[simp]
theorem WF.rhs0_lt_and :
    rhs0.var < var := by
  grind

@[simp]
theorem WF.rhs1_lt_and :
    rhs1.var < var := by
  grind

theorem WF.rhs0_lt_and_of_le (lt : var ≤ var') :
    rhs0.var < var' := by
  grind

grind_pattern WF.rhs0_lt_and_of_le => rhs0.var < var', Node.and rhs0 rhs1, aig.nodes[var]
grind_pattern WF.rhs0_lt_and_of_le => rhs0.var ≤ var', Node.and rhs0 rhs1, aig.nodes[var]

theorem WF.rhs1_lt_and_of_le (lt : var ≤ var') :
    rhs1.var < var' := by
  grind

grind_pattern WF.rhs1_lt_and_of_le => rhs1.var < var', Node.and rhs0 rhs1, aig.nodes[var]
grind_pattern WF.rhs1_lt_and_of_le => rhs1.var ≤ var', Node.and rhs0 rhs1, aig.nodes[var]

@[simp]
theorem WF.rhs0_mem_nodes_and :
    rhs0.var ∈ aig.nodes := by
  grind

grind_pattern WF.rhs0_mem_nodes_and => rhs0.var.validIn aig, Node.and rhs0 rhs1, aig.nodes[var]

@[simp]
theorem WF.rhs1_mem_nodes_and :
    rhs1.var ∈ aig.nodes := by
  grind

grind_pattern WF.rhs1_mem_nodes_and => rhs1.var.validIn aig, Node.and rhs0 rhs1, aig.nodes[var]

end AcyclicGates

/--
  The reset function of the Aig is acyclic.
  This is enfoced by requiring each latch's reset to have a lower variable
  index than the latch's output.
-/
@[expose, local grind, local simp]
def AcyclicResets (aig : Aig) : Prop :=
  ∀ idx (_ : idx ∈ aig.latches),
    match aig.latches[idx].reset with
    | none => True
    | some lit => lit.var < aig.latches[idx].var

theorem WF.ResetsValid_of_LatchesValid_AcyclicReset {aig : Aig}
    (latchesValid : aig.LatchesValid)
    (acyclicResets : aig.AcyclicResets) :
    aig.ResetsValid := by
  grind

@[simp]
theorem WF.reset_lt_var (acyclicResets : aig.AcyclicResets) {idx : LatchIdx} (mem : idx ∈ aig.latches)
    {lit : Lit} (isSome : aig.latches[idx].reset = some lit) :
    lit.var < aig.latches[idx].var := by
  grind

theorem WF.reset_lt_var_of_le (acyclicResets : aig.AcyclicResets) {var : Var} {idx : LatchIdx}
    (mem : idx ∈ aig.latches) (lt : aig.latches[idx].var ≤ var)
    {lit : Lit} (isSome : aig.latches[idx].reset = some lit) :
    lit.var < var := by
  grind

grind_pattern WF.reset_lt_var_of_le => aig.latches[idx], some lit, lit.var < var
grind_pattern WF.reset_lt_var_of_le => aig.latches[idx], some lit, lit.var ≤ var

/--
  All indices within the Aig are valid and the gates and reset function are
  acyclic, allowing the definition of semantics.
-/
@[local grind]
structure WF (aig : Aig) : Prop where
  inputsValid : aig.InputsValid
  inputIdxsValid : aig.InputIdxsValid

  latchesValid : aig.LatchesValid
  latchIdxsValid : aig.LatchIdxsValid
  resetsValid : aig.ResetsValid
  nextsValid : aig.NextsValid

  acyclicGates : aig.AcyclicGates
  acyclicResets : aig.AcyclicResets

namespace WF

section triggers
variable (wf : aig.WF)
include wf

theorem InputsValid_of_WF    : aig.InputsValid    := wf.inputsValid
theorem InputIdxsValid_of_WF : aig.InputIdxsValid := wf.inputIdxsValid
theorem LatchesValid_of_WF   : aig.LatchesValid   := wf.latchesValid
theorem LatchIdxsValid_of_WF : aig.LatchIdxsValid := wf.latchIdxsValid
theorem ResetsValid_of_WF    : aig.ResetsValid    := wf.resetsValid
theorem NextsValid_of_WF     : aig.NextsValid     := wf.nextsValid
theorem AcyclicGates_of_WF   : aig.AcyclicGates   := wf.acyclicGates
theorem AcyclicResets_of_WF  : aig.AcyclicResets  := wf.acyclicResets

grind_pattern AcyclicResets_of_WF  => aig.WF, aig.AcyclicResets
grind_pattern AcyclicGates_of_WF   => aig.WF, aig.AcyclicGates
grind_pattern InputsValid_of_WF    => aig.WF, aig.InputsValid
grind_pattern InputIdxsValid_of_WF => aig.WF, aig.InputIdxsValid
grind_pattern LatchesValid_of_WF   => aig.WF, aig.LatchesValid
grind_pattern LatchIdxsValid_of_WF => aig.WF, aig.LatchIdxsValid
grind_pattern ResetsValid_of_WF    => aig.WF, aig.ResetsValid
grind_pattern NextsValid_of_WF     => aig.WF, aig.NextsValid

end triggers

/-
  `empty`.
-/
section empty

@[simp, grind .] theorem InputsValid_empty    : empty.InputsValid    := by grind
@[simp, grind .] theorem InputIdxsValid_empty : empty.InputIdxsValid := by grind
@[simp, grind .] theorem LatchesValid_empty   : empty.LatchesValid   := by grind
@[simp, grind .] theorem LatchIdxsValid_empty : empty.LatchIdxsValid := by grind
@[simp, grind .] theorem ResetsValid_empty    : empty.ResetsValid    := by grind
@[simp, grind .] theorem NextsValid_empty     : empty.NextsValid     := by grind
@[simp, grind .] theorem AcyclicGates_empty   : empty.AcyclicGates   := by grind
@[simp, grind .] theorem AcyclicResets_empty  : empty.AcyclicResets  := by grind
@[simp, grind .] theorem WF_empty             : empty.WF             := by grind

end empty

/-
  `LatchIdx.setNext`.
-/
section latch_setNext
variable {idx : LatchIdx} {next : Lit} (valid : idx.validIn aig)

@[simp, grind .]
theorem InputsValid_setNext
    (inputsValid : aig.InputsValid) :
    (idx.setNext aig next).InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_setNext
    (inputIdxsValid : aig.InputIdxsValid) :
    (idx.setNext aig next valid).InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_setNext
    (latchesValid : aig.LatchesValid) :
    (idx.setNext aig next valid).LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_setNext
    (latchIdxsValid : aig.LatchIdxsValid) :
    (idx.setNext aig next valid).LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_setNext
    (resetsValid : aig.ResetsValid) :
    (idx.setNext aig next valid).ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_setNext
    (nextsValid : aig.NextsValid)
    (nextValid : next.validIn aig) :
    (idx.setNext aig next valid).NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_setNext
    (acyclicGates : aig.AcyclicGates) :
    (idx.setNext aig next valid).AcyclicGates := by
  grind

@[simp, grind .]
theorem AcyclicResets_setNext
    (acyclicResets : aig.AcyclicResets) :
    (idx.setNext aig next valid).AcyclicResets := by
  grind

@[simp, grind .]
theorem setNext
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig) :
    (idx.setNext aig next valid).WF := by
  grind

end latch_setNext

/-
  `LatchIdx.setReset`.
-/
section latch_setReset
variable {idx : LatchIdx} {reset : Option Lit} (valid : idx.validIn aig)

@[simp, grind .]
theorem InputsValid_setReset
    (inputsValid : aig.InputsValid) :
    (idx.setReset aig reset).InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_setReset
    (inputIdxsValid : aig.InputIdxsValid) :
    (idx.setReset aig reset valid).InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_setReset
    (latchesValid : aig.LatchesValid) :
    (idx.setReset aig reset valid).LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_setReset
    (latchIdxsValid : aig.LatchIdxsValid) :
    (idx.setReset aig reset valid).LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_setReset_none
    (resetsValid : aig.ResetsValid) :
    (idx.setReset aig none valid).ResetsValid := by
  grind

@[simp]
theorem ResetsValid_setReset_some {reset : Lit}
    (resetsValid : aig.ResetsValid)
    (resetValid : reset.validIn aig) :
    (idx.setReset aig reset valid).ResetsValid := by
  grind

@[grind .]
theorem ResetsValid_setReset
    (resetsValid : aig.ResetsValid)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.validIn aig) :
    (idx.setReset aig reset valid).ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_setReset
    (nextsValid : aig.NextsValid) :
    (idx.setReset aig reset valid).NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_setReset
    (acyclicGates : aig.AcyclicGates) :
    (idx.setReset aig reset valid).AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_setReset_none
    (acyclicResets : aig.AcyclicResets) :
    (idx.setReset aig none valid).AcyclicResets := by
  grind

@[simp]
theorem AcyclicResets_setReset_some {reset : Lit}
    (acyclicResets : aig.AcyclicResets)
    (resetAcyclic : reset.var < idx.getVar aig) :
    (idx.setReset aig reset valid).AcyclicResets := by
  grind

@[grind .]
theorem AcyclicResets_setReset
    (acyclicResets : aig.AcyclicResets)
    (resetAcyclic :
      match reset with
      | none => True
      | some lit => lit.var < idx.getVar aig) :
    (idx.setReset aig reset valid).AcyclicResets := by
  grind

@[simp]
theorem setReset_none
    (wellFormed : aig.WF) :
    (idx.setReset aig none valid).WF := by
  grind

@[simp]
theorem setReset_some {reset : Lit}
    (wellFormed : aig.WF)
    (resetAcyclic : reset.var < idx.getVar aig) :
    (idx.setReset aig reset valid).WF := by
  grind

@[grind .]
theorem setReset
    (wellFormed : aig.WF)
    (resetAcyclic :
      match reset with
      | none => True
      | some lit => lit.var < idx.getVar aig) :
    (idx.setReset aig reset valid).WF := by
  grind

end latch_setReset

/-
  `addInput`
-/
section addInput

@[simp, grind .]
theorem InputsValid_addInput
    (inputsValid : aig.InputsValid) :
    aig.addInput.fst.InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_addInput
    (inputIdxsValid : aig.InputIdxsValid) :
    aig.addInput.fst.InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_addInput
    (latchesValid : aig.LatchesValid) :
    aig.addInput.fst.LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_addInput
    (latchIdxsValid : aig.LatchIdxsValid) :
    aig.addInput.fst.LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_addInput
    (resetsValid : aig.ResetsValid) :
    aig.addInput.fst.ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_addInput
    (nextsValid : aig.NextsValid) :
    aig.addInput.fst.NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_addInput
    (acyclicGates : aig.AcyclicGates) :
    aig.addInput.fst.AcyclicGates := by
  grind

@[simp, grind .]
theorem AcyclicResets_addInput
    (acyclicResets : aig.AcyclicResets) :
    aig.addInput.fst.AcyclicResets := by
  grind

@[simp, grind .]
theorem addInput
    (wellFormed : aig.WF) :
    aig.addInput.fst.WF := by
  grind

end addInput

/-
  `addLatch`
-/
section addLatch
variable {next : Lit} {reset : Option Lit}

@[simp, grind .]
theorem InputsValid_addLatch
    (inputsValid : aig.InputsValid) :
    (aig.addLatch next reset).fst.InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_addLatch
    (inputIdxsValid : aig.InputIdxsValid) :
    (aig.addLatch next reset).fst.InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_addLatch
    (latchesValid : aig.LatchesValid) :
    (aig.addLatch next reset).fst.LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_addLatch
    (latchIdxsValid : aig.LatchIdxsValid) :
    (aig.addLatch next reset).fst.LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_addLatch_none
    (resetsValid : aig.ResetsValid) :
    (aig.addLatch next none).fst.ResetsValid := by
  grind

@[simp]
theorem ResetsValid_addLatch_some {reset : Lit}
    (resetsValid : aig.ResetsValid)
    (resetValid : reset.validIn aig) :
    (aig.addLatch next reset).fst.ResetsValid := by
  grind

@[grind .]
theorem ResetsValid_addLatch
    (resetsValid : aig.ResetsValid)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.validIn aig) :
    (aig.addLatch next reset).fst.ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_addLatch
    (nextsValid : aig.NextsValid)
    (nextValid : next.validIn aig) :
    (aig.addLatch next reset).fst.NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_addLatch
    (acyclicGates : aig.AcyclicGates) :
    (aig.addLatch next reset).fst.AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_addLatch_none
    (acyclicResets : aig.AcyclicResets) :
    (aig.addLatch next none).fst.AcyclicResets := by
  grind

@[simp]
theorem AcyclicResets_addLatch_some {reset : Lit}
    (acyclicResets : aig.AcyclicResets)
    (resetValid : reset.validIn aig) :
    (aig.addLatch next reset).fst.AcyclicResets := by
  grind

@[grind .]
theorem AcyclicResets_addLatch
    (acyclicResets : aig.AcyclicResets)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.validIn aig) :
    (aig.addLatch next reset).fst.AcyclicResets := by
  grind

@[simp]
theorem addLatch_none
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig) :
    (aig.addLatch next none).fst.WF := by
  grind

@[simp]
theorem addLatch_some {reset : Lit}
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig)
    (resetValid : reset.validIn aig) :
    (aig.addLatch next reset).fst.WF := by
  grind

@[grind .]
theorem addLatch
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.validIn aig) :
    (aig.addLatch next reset).fst.WF := by
  grind

end addLatch

/-
  `addAnd`
-/
section addAnd
variable {rhs0 rhs1 : Lit}

@[simp, grind .]
theorem InputsValid_addAnd
    (inputsValid : aig.InputsValid) :
    (aig.addAnd rhs0 rhs1).fst.InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_addAnd
    (inputIdxsValid : aig.InputIdxsValid)
    (h0 : rhs0.validIn aig)
    (h1 : rhs1.validIn aig) :
    (aig.addAnd rhs0 rhs1).fst.InputIdxsValid := by
  grind

theorem InputIdxsValid_addAnd'
    (inputIdxsValid : aig.InputIdxsValid)
    (h0 : rhs0.var ≠ aig.nextVar)
    (h1 : rhs1.var ≠ aig.nextVar) :
    (aig.addAnd rhs0 rhs1).fst.InputIdxsValid := by
    grind [nodes_addAnd']

@[simp, grind .]
theorem LatchesValid_addAnd
    (latchesValid : aig.LatchesValid) :
    (aig.addAnd rhs0 rhs1).fst.LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_addAnd
    (latchIdxsValid : aig.LatchIdxsValid)
    (h0 : rhs0.validIn aig)
    (h1 : rhs1.validIn aig) :
    (aig.addAnd rhs0 rhs1).fst.LatchIdxsValid := by
  grind

theorem LatchIdxsValid_addAnd'
    (inputIdxsValid : aig.LatchIdxsValid)
    (h0 : rhs0.var ≠ aig.nextVar)
    (h1 : rhs1.var ≠ aig.nextVar) :
    (aig.addAnd rhs0 rhs1).fst.LatchIdxsValid := by
    grind [nodes_addAnd']

@[simp, grind .]
theorem ResetsValid_addAnd
    (resetsValid : aig.ResetsValid) :
    (aig.addAnd rhs0 rhs1).fst.ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_addAnd
    (nextsValid : aig.NextsValid) :
    (aig.addAnd rhs0 rhs1).fst.NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_addAnd
    (acyclicGates : aig.AcyclicGates)
    (h0 : rhs0.validIn aig)
    (h1 : rhs1.validIn aig) :
    (aig.addAnd rhs0 rhs1).fst.AcyclicGates := by
  grind

@[simp, grind .]
theorem AcyclicResets_addAnd
    (acyclicResets : aig.AcyclicResets) :
    (aig.addAnd rhs0 rhs1).fst.AcyclicResets := by
  grind

@[simp, grind .]
theorem addAnd
    (wellFormed : aig.WF)
    (h0 : rhs0.validIn aig)
    (h1 : rhs1.validIn aig) :
    (aig.addAnd rhs0 rhs1).fst.WF := by
  grind

end addAnd

/-
  `InputIdx.convertToLatch`
-/
section input_convertToLatch
variable {idx : InputIdx} {next : Lit} {reset : Option Lit}
variable (valid : idx.validIn aig) (varValid : (idx.getVar aig valid).validIn aig)

@[simp, grind .]
theorem InputsValid_input_convertToLatch
    (inputsValid : aig.InputsValid) :
    (idx.convertToLatch aig next reset valid varValid).fst.InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_input_convertToLatch
    (inputIdxsValid : aig.InputIdxsValid) :
    (idx.convertToLatch aig next reset valid varValid).fst.InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_input_convertToLatch
    (latchesValid : aig.LatchesValid)
    (inputsValid  : aig.InputsValid) :
    (idx.convertToLatch aig next reset valid varValid).fst.LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_input_convertToLatch
    (latchIdxsValid : aig.LatchIdxsValid) :
    (idx.convertToLatch aig next reset valid varValid).fst.LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_input_convertToLatch_none
    (resetsValid : aig.ResetsValid) :
    (idx.convertToLatch aig next none valid varValid).fst.ResetsValid := by
  grind

@[simp]
theorem ResetsValid_input_convertToLatch_some {reset : Lit}
    (resetsValid : aig.ResetsValid)
    (resetValid : reset.validIn aig) :
    (idx.convertToLatch aig next reset valid varValid).fst.ResetsValid := by
  grind

@[grind .]
theorem ResetsValid_input_convertToLatch
    (resetsValid : aig.ResetsValid)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.validIn aig) :
    (idx.convertToLatch aig next reset valid varValid).fst.ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_input_convertToLatch
    (nextsValid : aig.NextsValid)
    (nextValid : next.validIn aig) :
    (idx.convertToLatch aig next reset valid varValid).fst.NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_input_convertToLatch
    (acyclicGates : aig.AcyclicGates) :
    (idx.convertToLatch aig next reset valid varValid).fst.AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_input_convertToLatch_none
    (acyclicResets : aig.AcyclicResets) :
    (idx.convertToLatch aig next none valid varValid).fst.AcyclicResets := by
  grind

@[simp]
theorem AcyclicResets_input_convertToLatch_some {reset : Lit}
    (acyclicResets : aig.AcyclicResets)
    (resetAcyclic : reset.var < idx.getVar aig) :
    (idx.convertToLatch aig next reset valid varValid).fst.AcyclicResets := by
  grind

@[grind .]
theorem AcyclicResets_input_convertToLatch
    (acyclicResets : aig.AcyclicResets)
    (resetAcyclic :
      match reset with
      | none => True
      | some lit => lit.var < idx.getVar aig) :
    (idx.convertToLatch aig next reset valid varValid).fst.AcyclicResets := by
  grind

@[simp]
theorem input_convertToLatch_none
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig) :
    (idx.convertToLatch aig next none valid varValid).fst.WF := by
  grind

@[simp]
theorem input_convertToLatch_some {reset : Lit}
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig)
    (resetAcyclic : reset.var < idx.getVar aig) :
    (idx.convertToLatch aig next reset valid varValid).fst.WF := by
  grind

@[grind .]
theorem input_convertToLatch
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig)
    (resetAcyclic :
      match reset with
      | none => True
      | some lit => lit.var < idx.getVar aig) :
    (idx.convertToLatch aig next reset valid varValid).fst.WF := by
  grind

end input_convertToLatch

/-
  `InputIdx.convertToAnd`
-/
section input_convertToAnd
variable {idx : InputIdx} {rhs0 rhs1 : Lit}
variable (valid : idx.validIn aig) (varValid : (idx.getVar aig valid).validIn aig)

@[simp, grind .]
theorem InputsValid_input_convertToAnd
    (inputsValid : aig.InputsValid)
    (h0 : rhs0.var ≠ idx.getVar aig)
    (h0 : rhs1.var ≠ idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_input_convertToAnd
    (inputIdxsValid : aig.InputIdxsValid)
    (h0 : rhs0.var ≠ idx.getVar aig)
    (h0 : rhs1.var ≠ idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_input_convertToAnd
    (latchesValid : aig.LatchesValid)
    (inputsValid  : aig.InputsValid)
    (h0 : rhs0.var ≠ idx.getVar aig)
    (h0 : rhs1.var ≠ idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_input_convertToAnd
    (latchIdxsValid : aig.LatchIdxsValid)
    (h0 : rhs0.var ≠ idx.getVar aig)
    (h0 : rhs1.var ≠ idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_input_convertToAnd
    (resetsValid : aig.ResetsValid)
    (h0 : rhs0.var ≠ idx.getVar aig)
    (h0 : rhs1.var ≠ idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_input_convertToAnd
    (nextsValid : aig.NextsValid)
    (h0 : rhs0.var ≠ idx.getVar aig)
    (h0 : rhs1.var ≠ idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_input_convertToAnd
    (acyclicGates : aig.AcyclicGates)
    (h0 : rhs0.var < idx.getVar aig)
    (h0 : rhs1.var < idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).AcyclicGates := by
  have : rhs0.var ≠ idx.getVar aig ∧ rhs1.var ≠ idx.getVar aig := by grind
  grind

@[simp, grind .]
theorem AcyclicResets_input_convertToAnd
    (acyclicResets : aig.AcyclicResets) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).AcyclicResets := by
  grind

@[simp, grind .]
theorem input_convertToAnd
    (wellFormed : aig.WF)
    (h0 : rhs0.var < idx.getVar aig)
    (h0 : rhs1.var < idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).WF := by
  have : rhs0.var ≠ idx.getVar aig ∧ rhs1.var ≠ idx.getVar aig := by grind
  grind

end input_convertToAnd

/-
  `InputIdx.changeIdx`
-/
section input_changeIdx
variable {old new : InputIdx}
variable (valid : old.validIn aig) (varValid : (old.getVar aig).validIn aig) (unused : ¬new.validIn aig ∨ old = new)

@[simp, grind .]
theorem InputsValid_input_changeIdx
    (inputsValid : aig.InputsValid) :
    (old.changeIdx new aig valid varValid unused).InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_input_changeIdx
    (inputIdxsValid : aig.InputIdxsValid) :
    (old.changeIdx new aig valid varValid unused).InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_input_changeIdx
    (latchesValid : aig.LatchesValid)
    (inputsValid : aig.InputsValid) :
    (old.changeIdx new aig valid varValid unused).LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_input_changeIdx
    (latchIdxsValid : aig.LatchIdxsValid) :
    (old.changeIdx new aig valid varValid unused).LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_input_changeIdx
    (resetsValid : aig.ResetsValid) :
    (old.changeIdx new aig valid varValid unused).ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_input_changeIdx
    (nextsValid : aig.NextsValid) :
    (old.changeIdx new aig valid varValid unused).NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_input_changeIdx
    (acyclicGates : aig.AcyclicGates) :
    (old.changeIdx new aig valid varValid unused).AcyclicGates := by
  grind

@[simp, grind .]
theorem AcyclicResets_input_changeIdx
    (acyclicResets : aig.AcyclicResets) :
    (old.changeIdx new aig valid varValid unused).AcyclicResets := by
  grind

@[simp, grind .]
theorem input_changeIdx
    (wellFormed : aig.WF) :
    (old.changeIdx new aig valid varValid unused).WF := by
  grind

end input_changeIdx

/-
  `LatchIdx.convertToInput`
-/
section latch_convertToInput
variable {idx : LatchIdx}
variable (valid : idx.validIn aig) (varValid : (idx.getVar aig valid).validIn aig)

@[simp, grind .]
theorem InputsValid_latch_convertToInput
    (inputsValid : aig.InputsValid)
    (latchesValid : aig.LatchesValid) :
    (idx.convertToInput aig valid varValid).fst.InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_latch_convertToInput
    (inputIdxsValid : aig.InputIdxsValid) :
    (idx.convertToInput aig valid varValid).fst.InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_latch_convertToInput
    (latchesValid : aig.LatchesValid) :
    (idx.convertToInput aig valid varValid).fst.LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_latch_convertToInput
    (latchIdxsValid : aig.LatchIdxsValid) :
    (idx.convertToInput aig valid varValid).fst.LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_latch_convertToInput
    (resetsValid : aig.ResetsValid) :
    (idx.convertToInput aig valid varValid).fst.ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_latch_convertToInput
    (nextsValid : aig.NextsValid) :
    (idx.convertToInput aig valid varValid).fst.NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_latch_convertToInput
    (acyclicGates : aig.AcyclicGates) :
    (idx.convertToInput aig valid varValid).fst.AcyclicGates := by
  grind

@[simp, grind .]
theorem AcyclicResets_latch_convertToInput
    (acyclicResets : aig.AcyclicResets) :
    (idx.convertToInput aig valid varValid).fst.AcyclicResets := by
  grind

@[simp, grind .]
theorem latch_convertToInput
    (wellFormed : aig.WF) :
    (idx.convertToInput aig valid varValid).fst.WF := by
  grind

end latch_convertToInput

/-
  `LatchIdx.convertToAnd`
-/
section latch_convertToAnd
variable {idx : LatchIdx} {rhs0 rhs1 : Lit}
variable (valid : idx.validIn aig) (varValid : (idx.getVar aig valid).validIn aig)

@[simp, grind .]
theorem InputsValid_latch_convertToAnd
    (inputsValid : aig.InputsValid)
    (latchesValid : aig.LatchesValid)
    (h0 : rhs0.var ≠ idx.getVar aig)
    (h0 : rhs1.var ≠ idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_latch_convertToAnd
    (inputIdxsValid : aig.InputIdxsValid)
    (h0 : rhs0.var ≠ idx.getVar aig)
    (h0 : rhs1.var ≠ idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_latch_convertToAnd
    (latchesValid : aig.LatchesValid)
    (h0 : rhs0.var ≠ idx.getVar aig)
    (h0 : rhs1.var ≠ idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_latch_convertToAnd
    (latchIdxsValid : aig.LatchIdxsValid)
    (h0 : rhs0.var ≠ idx.getVar aig)
    (h0 : rhs1.var ≠ idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_latch_convertToAnd
    (resetsValid : aig.ResetsValid)
    (h0 : rhs0.var ≠ idx.getVar aig)
    (h0 : rhs1.var ≠ idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_latch_convertToAnd
    (nextsValid : aig.NextsValid)
    (h0 : rhs0.var ≠ idx.getVar aig)
    (h0 : rhs1.var ≠ idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_latch_convertToAnd
    (acyclicGates : aig.AcyclicGates)
    (h0 : rhs0.var < idx.getVar aig)
    (h0 : rhs1.var < idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).AcyclicGates := by
  have : rhs0.var ≠ idx.getVar aig ∧ rhs1.var ≠ idx.getVar aig := by grind
  grind

@[simp, grind .]
theorem AcyclicResets_latch_convertToAnd
    (acyclicResets : aig.AcyclicResets) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).AcyclicResets := by
  grind

@[simp, grind .]
theorem latch_convertToAnd
    (wellFormed : aig.WF)
    (h0 : rhs0.var < idx.getVar aig)
    (h0 : rhs1.var < idx.getVar aig) :
    (idx.convertToAnd aig rhs0 rhs1 valid varValid).WF := by
  have : rhs0.var ≠ idx.getVar aig ∧ rhs1.var ≠ idx.getVar aig := by grind
  grind

end latch_convertToAnd

/-
  `LatchIdx.changeIdx`
-/
section latch_changeIdx
variable {old new : LatchIdx}
variable (valid : old.validIn aig) (varValid : (old.getVar aig).validIn aig) (unused : ¬new.validIn aig ∨ old = new)

@[simp, grind .]
theorem InputsValid_latch_changeIdx
    (inputsValid : aig.InputsValid)
    (latchesValid : aig.LatchesValid) :
    (old.changeIdx new aig valid varValid unused).InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_latch_changeIdx
    (inputIdxsValid : aig.InputIdxsValid) :
    (old.changeIdx new aig valid varValid unused).InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_latch_changeIdx
    (latchesValid : aig.LatchesValid) :
    (old.changeIdx new aig valid varValid unused).LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_latch_changeIdx
    (latchIdxsValid : aig.LatchIdxsValid) :
    (old.changeIdx new aig valid varValid unused).LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_latch_changeIdx
    (resetsValid : aig.ResetsValid) :
    (old.changeIdx new aig valid varValid unused).ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_latch_changeIdx
    (nextsValid : aig.NextsValid) :
    (old.changeIdx new aig valid varValid unused).NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_latch_changeIdx
    (acyclicGates : aig.AcyclicGates) :
    (old.changeIdx new aig valid varValid unused).AcyclicGates := by
  grind

@[simp, grind .]
theorem AcyclicResets_latch_changeIdx
    (acyclicResets : aig.AcyclicResets) :
    (old.changeIdx new aig valid varValid unused).AcyclicResets := by
  grind

@[simp, grind .]
theorem latch_changeIdx
    (wellFormed : aig.WF) :
    (old.changeIdx new aig valid varValid unused).WF := by
  grind

end latch_changeIdx

/-
  `convertAndToInput`
-/
section convertAndToInput
variable {var : Var} (valid : var.validIn aig)

@[simp, grind .]
theorem InputsValid_convertAndToInput isAnd
    (inputsValid : aig.InputsValid) :
    (aig.convertAndToInput var valid isAnd).fst.InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_convertAndToInput isAnd
    (inputIdxsValid : aig.InputIdxsValid) :
    (aig.convertAndToInput var valid isAnd).fst.InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_convertAndToInput isAnd
    (latchesValid : aig.LatchesValid) :
    (aig.convertAndToInput var valid isAnd).fst.LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_convertAndToInput isAnd
    (latchIdxsValid : aig.LatchIdxsValid) :
    (aig.convertAndToInput var valid isAnd).fst.LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_convertAndToInput isAnd
    (resetsValid : aig.ResetsValid) :
    (aig.convertAndToInput var valid isAnd).fst.ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_convertAndToInput isAnd
    (nextsValid : aig.NextsValid) :
    (aig.convertAndToInput var valid isAnd).fst.NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_convertAndToInput isAnd
    (acyclicGates : aig.AcyclicGates) :
    (aig.convertAndToInput var valid isAnd).fst.AcyclicGates := by
  grind

@[simp, grind .]
theorem AcyclicResets_convertAndToInput isAnd
    (acyclicResets : aig.AcyclicResets) :
    (aig.convertAndToInput var valid isAnd).fst.AcyclicResets := by
  grind

@[simp, grind .]
theorem convertAndToInput isAnd
    (wellFormed : aig.WF) :
    (aig.convertAndToInput var valid isAnd).fst.WF := by
  grind

end convertAndToInput

/-
  `convertAndToLatch`
-/
section convertAndToLatch
variable {var : Var} {next : Lit} {reset : Option Lit} (valid : var.validIn aig)

@[simp, grind .]
theorem InputsValid_convertAndToLatch isAnd
    (inputsValid : aig.InputsValid) :
    (aig.convertAndToLatch var next reset valid isAnd).fst.InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_convertAndToLatch isAnd
    (inputIdxsValid : aig.InputIdxsValid) :
    (aig.convertAndToLatch var next reset valid isAnd).fst.InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_convertAndToLatch isAnd
    (latchesValid : aig.LatchesValid) :
    (aig.convertAndToLatch var next reset valid isAnd).fst.LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_convertAndToLatch isAnd
    (latchIdxsValid : aig.LatchIdxsValid) :
    (aig.convertAndToLatch var next reset valid isAnd).fst.LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_convertAndToLatch_none isAnd
    (resetsValid : aig.ResetsValid) :
    (aig.convertAndToLatch var next none valid isAnd).fst.ResetsValid := by
  grind

@[simp]
theorem ResetsValid_convertAndToLatch_some isAnd {reset : Lit}
    (resetsValid : aig.ResetsValid)
    (resetValid : reset.validIn aig) :
    (aig.convertAndToLatch var next reset valid isAnd).fst.ResetsValid := by
  grind

@[grind .]
theorem ResetsValid_convertAndToLatch isAnd
    (resetsValid : aig.ResetsValid)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.validIn aig) :
    (aig.convertAndToLatch var next reset valid isAnd).fst.ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_convertAndToLatch isAnd
    (nextsValid : aig.NextsValid)
    (nextValid : next.validIn aig) :
    (aig.convertAndToLatch var next reset valid isAnd).fst.NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_convertAndToLatch isAnd
    (acyclicGates : aig.AcyclicGates) :
    (aig.convertAndToLatch var next reset valid isAnd).fst.AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_convertAndToLatch_none isAnd
    (acyclicResets : aig.AcyclicResets) :
    (aig.convertAndToLatch var next none valid isAnd).fst.AcyclicResets := by
  grind

@[simp]
theorem AcyclicResets_convertAndToLatch_some isAnd {reset : Lit}
    (acyclicResets : aig.AcyclicResets)
    (resetAcyclic : reset.var < var) :
    (aig.convertAndToLatch var next reset valid isAnd).fst.AcyclicResets := by
  grind

@[grind .]
theorem AcyclicResets_convertAndToLatch isAnd
    (acyclicResets : aig.AcyclicResets)
    (resetAcyclic :
      match reset with
      | none => True
      | some lit => lit.var < var) :
    (aig.convertAndToLatch var next reset valid isAnd).fst.AcyclicResets := by
  grind

@[simp]
theorem convertAndToLatch_none isAnd
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig) :
    (aig.convertAndToLatch var next none valid isAnd).fst.WF := by
  grind

@[simp]
theorem convertAndToLatch_some isAnd {reset : Lit}
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig)
    (resetAcyclic : reset.var < var) :
    (aig.convertAndToLatch var next reset valid isAnd).fst.WF := by
  grind

@[grind .]
theorem convertAndToLatch isAnd
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig)
    (resetAcyclic :
      match reset with
      | none => True
      | some lit => lit.var < var) :
    (aig.convertAndToLatch var next reset valid isAnd).fst.WF := by
  grind

end convertAndToLatch

/-
  `rewriteAnd`
-/
section rewriteAnd
variable {var : Var} {rhs0 rhs1 : Lit} (valid : var.validIn aig)

@[simp, grind .]
theorem InputsValid_rewriteAnd isAnd
    (inputsValid : aig.InputsValid)
    (h0 : rhs0.var ≠ var)
    (h0 : rhs1.var ≠ var) :
    (aig.rewriteAnd var rhs0 rhs1 valid isAnd).InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_rewriteAnd isAnd
    (inputIdxsValid : aig.InputIdxsValid)
    (h0 : rhs0.var ≠ var)
    (h0 : rhs1.var ≠ var) :
    (aig.rewriteAnd var rhs0 rhs1 valid isAnd).InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_rewriteAnd isAnd
    (latchesValid : aig.LatchesValid)
    (h0 : rhs0.var ≠ var)
    (h0 : rhs1.var ≠ var) :
    (aig.rewriteAnd var rhs0 rhs1 valid isAnd).LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_rewriteAnd isAnd
    (latchIdxsValid : aig.LatchIdxsValid)
    (h0 : rhs0.var ≠ var)
    (h0 : rhs1.var ≠ var) :
    (aig.rewriteAnd var rhs0 rhs1 valid isAnd).LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_rewriteAnd isAnd
    (resetsValid : aig.ResetsValid)
    (h0 : rhs0.var ≠ var)
    (h0 : rhs1.var ≠ var) :
    (aig.rewriteAnd var rhs0 rhs1 valid isAnd).ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_rewriteAnd isAnd
    (nextsValid : aig.NextsValid)
    (h0 : rhs0.var ≠ var)
    (h0 : rhs1.var ≠ var) :
    (aig.rewriteAnd var rhs0 rhs1 valid isAnd).NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_rewriteAnd isAnd
    (acyclicGates : aig.AcyclicGates)
    (h0 : rhs0.var < var)
    (h0 : rhs1.var < var) :
    (aig.rewriteAnd var rhs0 rhs1 valid isAnd).AcyclicGates := by
  have : rhs0.var ≠ var ∧ rhs1.var ≠ var := by grind
  grind

@[simp, grind .]
theorem AcyclicResets_rewriteAnd isAnd
    (acyclicResets : aig.AcyclicResets) :
    (aig.rewriteAnd var rhs0 rhs1 valid isAnd).AcyclicResets := by
  grind

@[simp, grind .]
theorem rewriteAnd isAnd
    (wellFormed : aig.WF)
    (h0 : rhs0.var < var)
    (h0 : rhs1.var < var) :
    (aig.rewriteAnd var rhs0 rhs1 valid isAnd).WF := by
  have : rhs0.var ≠ var ∧ rhs1.var ≠ var := by grind
  grind

end rewriteAnd

end WF

end Valaig.Aig
