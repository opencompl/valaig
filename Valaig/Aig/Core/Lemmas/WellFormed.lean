module

public import Valaig.Aig.Core.Basic
import Valaig.Aig.Core.Lemmas.Basic
import Valaig.Aig.Core.Lemmas.Modify
import Valaig.Aig.Core.Lemmas.Monotone
import all Valaig.Aig.Core.Basic

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
@[expose, local grind]
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
@[expose, local grind]
def InputIdxsValid (aig : Aig) : Prop :=
  ∀ var (_ : var ∈ aig.nodes) idx,
    aig[var] = .input idx → ∃ _, aig.inputs[idx].var = var

@[simp]
theorem WF.mem_inputs_of_node {inputIdxsValid : aig.InputIdxsValid} {var : Var} {idx : InputIdx}
    (mem : var ∈ aig.nodes) (eq : aig[var]'mem = .input idx) :
    idx ∈ aig.inputs := by
  grind

grind_pattern WF.mem_inputs_of_node => idx ∈ aig.inputs, aig[var]'mem, Node.input idx

@[simp]
theorem WF.var_inputs_of_node {inputIdxsValid : aig.InputIdxsValid} {var : Var} {idx : InputIdx}
    (mem : var ∈ aig.nodes) (eq : aig[var]'mem = .input idx) mem' :
    (aig.inputs[idx]'mem').var = var := by
  grind

grind_pattern WF.var_inputs_of_node => (aig.inputs[idx]'mem').var, aig[var]'mem, Node.input idx

/--
  All latch indices point to a latch in the Aig.
-/
@[expose, local grind]
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
@[expose, local grind]
def LatchIdxsValid (aig : Aig) : Prop :=
  ∀ var (_ : var ∈ aig.nodes) idx,
    aig[var] = .latch idx → ∃ _, aig.latches[idx].var = var

@[simp]
theorem WF.mem_latches_of_node {latchIdxsValid : aig.LatchIdxsValid} {var : Var} {idx : LatchIdx}
    (mem : var ∈ aig.nodes) (eq : aig[var]'mem = .latch idx) :
    idx ∈ aig.latches := by
  grind

grind_pattern WF.mem_latches_of_node => idx ∈ aig.latches, aig[var]'mem, Node.latch idx

@[simp]
theorem WF.var_latches_of_node {latchIdxsValid : aig.LatchIdxsValid} {var : Var} {idx : LatchIdx}
    (mem : var ∈ aig.nodes) (eq : aig[var]'mem = .latch idx) mem' :
    (aig.latches[idx]'mem').var = var := by
  grind

grind_pattern WF.var_latches_of_node => (aig.latches[idx]'mem').var, aig[var]'mem, Node.latch idx

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
@[expose, local grind]
def ResetsValid (aig : Aig) : Prop :=
  ∀ idx (_ : idx ∈ aig.latches),
    match aig.latches[idx].reset with
    | none => True
    | some lit => lit.validIn aig

@[simp]
theorem WF.mem_nodes_reset {resetsValid : aig.ResetsValid} {idx : LatchIdx} (mem : idx ∈ aig.latches)
    {lit : Lit} (isSome : (aig.latches[idx]'mem).reset = some lit) :
    lit.validIn aig := by
  grind

grind_pattern WF.mem_nodes_reset => (aig.latches[idx]'mem).reset, some lit, lit.validIn aig

/--
  All latch next state literals are valid in the Aig.
-/
@[expose, local grind]
def NextsValid (aig : Aig) : Prop :=
  ∀ idx (_ : idx ∈ aig.latches),
    aig.latches[idx].next.validIn aig

@[simp, grind .]
theorem WF.mem_nodes_next {nextsValid : aig.NextsValid} {idx : LatchIdx} (mem : idx ∈ aig.latches) :
    (aig.latches[idx]'mem).next.validIn aig := by
  grind

/--
  The gates of the Aig are acyclic.
  This is enforced by requiring each gate's inputs to have lower variable
  indices than themselves.
-/
@[expose, local grind]
def AcyclicGates (aig : Aig) : Prop :=
  ∀ {var : Var} {lhs rhs} (mem : var ∈ aig.nodes),
    aig.nodes[var] = .and lhs rhs → lhs.var < var ∧ rhs.var < var

section AcyclicGates
variable {acyclicGates : aig.AcyclicGates} {var var' : Var} {lhs rhs : Lit}
variable (mem : var ∈ aig.nodes) (eq : aig.nodes[var]'mem = .and lhs rhs)
include acyclicGates mem eq

@[simp]
theorem WF.lhs_lt_and :
    lhs.var < var := by
  grind

@[simp]
theorem WF.rhs_lt_and :
    rhs.var < var := by
  grind

theorem WF.lhs_lt_and_of_le (lt : var ≤ var') :
    lhs.var < var' := by
  grind

grind_pattern WF.lhs_lt_and_of_le => lhs.var < var', Node.and lhs rhs, aig.nodes[var]'mem

theorem WF.rhs_lt_and_of_le (lt : var ≤ var') :
    rhs.var < var' := by
  grind

grind_pattern WF.rhs_lt_and_of_le => rhs.var < var', Node.and lhs rhs, aig.nodes[var]'mem

theorem WF.lhs_idx_lt_and_of_le {n : Nat} (lt : var.idx ≤ n) :
    lhs.var.idx < n := by
  grind

grind_pattern WF.lhs_idx_lt_and_of_le => lhs.var.idx < n, Node.and lhs rhs, aig.nodes[var]'mem
grind_pattern WF.lhs_idx_lt_and_of_le => n ≤ lhs.var.idx, Node.and lhs rhs, aig.nodes[var]'mem

theorem WF.rhs_idx_lt_and_of_le {n : Nat} (lt : var.idx ≤ n) :
    rhs.var.idx < n := by
  grind

grind_pattern WF.rhs_idx_lt_and_of_le => rhs.var.idx < n, Node.and lhs rhs, aig.nodes[var]'mem
grind_pattern WF.rhs_idx_lt_and_of_le => n ≤ rhs.var.idx, Node.and lhs rhs, aig.nodes[var]'mem

@[simp]
theorem WF.lhs_mem_nodes_and :
    lhs.var ∈ aig.nodes := by
  grind

grind_pattern WF.lhs_mem_nodes_and => lhs.var.validIn aig, Node.and lhs rhs, aig.nodes[var]'mem

@[simp]
theorem WF.rhs_mem_nodes_and :
    rhs.var ∈ aig.nodes := by
  grind

grind_pattern WF.rhs_mem_nodes_and => rhs.var.validIn aig, Node.and lhs rhs, aig.nodes[var]'mem

end AcyclicGates

/--
  The reset function of the Aig is acyclic.
  This is enfoced by requiring each latch's reset to have a lower variable
  index than the latch's output.
-/
@[expose, local grind]
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
    {lit : Lit} (isSome : (aig.latches[idx]'mem).reset = some lit) :
    lit.var < (aig.latches[idx]'mem).var := by
  grind

theorem WF.reset_lt_var_of_le (acyclicResets : aig.AcyclicResets) {var : Var} {idx : LatchIdx}
    (mem : idx ∈ aig.latches) (lt : (aig.latches[idx]'mem).var ≤ var)
    {lit : Lit} (isSome : (aig.latches[idx]'mem).reset = some lit) :
    lit.var < var := by
  grind

grind_pattern WF.reset_lt_var_of_le => (aig.latches[idx]'mem).reset, some lit, lit.var < var
grind_pattern WF.reset_lt_var_of_le => (aig.latches[idx]'mem).reset, some lit, lit.var ≤ var

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
  `setNext`.
-/
section setNext
variable {idx : LatchIdx} {next : Lit} (valid : idx.validIn aig)

@[simp, grind .]
theorem InputsValid_setNext
    (inputsValid : aig.InputsValid) :
    (aig.setNext idx next).InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_setNext
    (inputIdxsValid : aig.InputIdxsValid) :
    (aig.setNext idx next valid).InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_setNext
    (latchesValid : aig.LatchesValid) :
    (aig.setNext idx next valid).LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_setNext
    (latchIdxsValid : aig.LatchIdxsValid) :
    (aig.setNext idx next valid).LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_setNext
    (resetsValid : aig.ResetsValid) :
    (aig.setNext idx next valid).ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_setNext
    (nextsValid : aig.NextsValid)
    (nextValid : next.validIn aig) :
    (aig.setNext idx next valid).NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_setNext
    (acyclicGates : aig.AcyclicGates) :
    (aig.setNext idx next valid).AcyclicGates := by
  grind

@[simp, grind .]
theorem AcyclicResets_setNext
    (acyclicResets : aig.AcyclicResets) :
    (aig.setNext idx next valid).AcyclicResets := by
  grind

@[simp, grind .]
theorem setNext
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig) :
    (aig.setNext idx next valid).WF := by
  grind

end setNext

/-
  `setReset`.
-/
section setReset
variable {idx : LatchIdx} {reset : Option Lit} (valid : idx.validIn aig)

@[simp, grind .]
theorem InputsValid_setReset
    (inputsValid : aig.InputsValid) :
    (aig.setReset idx reset).InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_setReset
    (inputIdxsValid : aig.InputIdxsValid) :
    (aig.setReset idx reset valid).InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_setReset
    (latchesValid : aig.LatchesValid) :
    (aig.setReset idx reset valid).LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_setReset
    (latchIdxsValid : aig.LatchIdxsValid) :
    (aig.setReset idx reset valid).LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_setReset_none
    (resetsValid : aig.ResetsValid) :
    (aig.setReset idx none valid).ResetsValid := by
  grind

@[simp]
theorem ResetsValid_setReset_some {reset : Lit}
    (resetsValid : aig.ResetsValid)
    (resetValid : reset.validIn aig) :
    (aig.setReset idx reset valid).ResetsValid := by
  grind

@[grind .]
theorem ResetsValid_setReset
    (resetsValid : aig.ResetsValid)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.validIn aig) :
    (aig.setReset idx reset valid).ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_setReset
    (nextsValid : aig.NextsValid) :
    (aig.setReset idx reset valid).NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_setReset
    (acyclicGates : aig.AcyclicGates) :
    (aig.setReset idx reset valid).AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_setReset_none
    (acyclicResets : aig.AcyclicResets) :
    (aig.setReset idx none valid).AcyclicResets := by
  grind

@[simp]
theorem AcyclicResets_setReset_some {reset : Lit}
    (acyclicResets : aig.AcyclicResets)
    (resetAcyclic : reset.var < idx.getVar aig) :
    (aig.setReset idx reset valid).AcyclicResets := by
  grind

@[grind .]
theorem AcyclicResets_setReset
    (acyclicResets : aig.AcyclicResets)
    (resetAcyclic :
      match reset with
      | none => True
      | some lit => lit.var < idx.getVar aig) :
    (aig.setReset idx reset valid).AcyclicResets := by
  grind

@[simp]
theorem setReset_none
    (wellFormed : aig.WF) :
    (aig.setReset idx none valid).WF := by
  grind

@[simp]
theorem setReset_some {reset : Lit}
    (wellFormed : aig.WF)
    (resetAcyclic : reset.var < idx.getVar aig) :
    (aig.setReset idx reset valid).WF := by
  grind

@[grind .]
theorem setReset
    (wellFormed : aig.WF)
    (resetAcyclic :
      match reset with
      | none => True
      | some lit => lit.var < idx.getVar aig) :
    (aig.setReset idx reset valid).WF := by
  grind

end setReset

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
  `addAndRaw`
-/
section addAndRaw
variable {lhs rhs : Lit}

@[simp, grind .]
theorem InputsValid_addAndRaw
    (inputsValid : aig.InputsValid) :
    (aig.addAndRaw lhs rhs).fst.InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_addAndRaw
    (inputIdxsValid : aig.InputIdxsValid)
    (h0 : lhs.validIn aig)
    (h1 : rhs.validIn aig) :
    (aig.addAndRaw lhs rhs).fst.InputIdxsValid := by
  grind

theorem InputIdxsValid_addAndRaw'
    (inputIdxsValid : aig.InputIdxsValid)
    (h0 : lhs.var ≠ aig.nextVar)
    (h1 : rhs.var ≠ aig.nextVar) :
    (aig.addAndRaw lhs rhs).fst.InputIdxsValid := by
    grind [nodes_addAndRaw']

@[simp, grind .]
theorem LatchesValid_addAndRaw
    (latchesValid : aig.LatchesValid) :
    (aig.addAndRaw lhs rhs).fst.LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_addAndRaw
    (latchIdxsValid : aig.LatchIdxsValid)
    (h0 : lhs.validIn aig)
    (h1 : rhs.validIn aig) :
    (aig.addAndRaw lhs rhs).fst.LatchIdxsValid := by
  grind

theorem LatchIdxsValid_addAndRaw'
    (inputIdxsValid : aig.LatchIdxsValid)
    (h0 : lhs.var ≠ aig.nextVar)
    (h1 : rhs.var ≠ aig.nextVar) :
    (aig.addAndRaw lhs rhs).fst.LatchIdxsValid := by
    grind [nodes_addAndRaw']

@[simp, grind .]
theorem ResetsValid_addAndRaw
    (resetsValid : aig.ResetsValid) :
    (aig.addAndRaw lhs rhs).fst.ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_addAndRaw
    (nextsValid : aig.NextsValid) :
    (aig.addAndRaw lhs rhs).fst.NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_addAndRaw
    (acyclicGates : aig.AcyclicGates)
    (h0 : lhs.validIn aig)
    (h1 : rhs.validIn aig) :
    (aig.addAndRaw lhs rhs).fst.AcyclicGates := by
  grind

@[simp, grind .]
theorem AcyclicResets_addAndRaw
    (acyclicResets : aig.AcyclicResets) :
    (aig.addAndRaw lhs rhs).fst.AcyclicResets := by
  grind

@[simp, grind .]
theorem addAndRaw
    (wellFormed : aig.WF)
    (h0 : lhs.validIn aig)
    (h1 : rhs.validIn aig) :
    (aig.addAndRaw lhs rhs).fst.WF := by
  grind

end addAndRaw

/-
  `addAnd`
-/
section addAnd
variable {lhs rhs : Lit}
attribute [local grind! .] getElem_nodes_addAnd

@[simp, grind .]
theorem InputsValid_addAnd
    (inputsValid : aig.InputsValid) :
    (aig.addAnd lhs rhs).fst.InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_addAnd
    (inputIdxsValid : aig.InputIdxsValid)
    (h0 : lhs.validIn aig)
    (h1 : rhs.validIn aig) :
    (aig.addAnd lhs rhs).fst.InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_addAnd
    (latchesValid : aig.LatchesValid) :
    (aig.addAnd lhs rhs).fst.LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_addAnd
    (latchIdxsValid : aig.LatchIdxsValid)
    (h0 : lhs.validIn aig)
    (h1 : rhs.validIn aig) :
    (aig.addAnd lhs rhs).fst.LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_addAnd
    (resetsValid : aig.ResetsValid) :
    (aig.addAnd lhs rhs).fst.ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_addAnd
    (nextsValid : aig.NextsValid) :
    (aig.addAnd lhs rhs).fst.NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_addAnd
    (acyclicGates : aig.AcyclicGates)
    (h0 : lhs.validIn aig)
    (h1 : rhs.validIn aig) :
    (aig.addAnd lhs rhs).fst.AcyclicGates := by
  grind [addAnd]

@[simp, grind .]
theorem AcyclicResets_addAnd
    (acyclicResets : aig.AcyclicResets) :
    (aig.addAnd lhs rhs).fst.AcyclicResets := by
  grind

@[simp, grind .]
theorem addAnd
    (wellFormed : aig.WF)
    (h0 : lhs.validIn aig)
    (h1 : rhs.validIn aig) :
    (aig.addAnd lhs rhs).fst.WF := by
  grind

end addAnd

/-
  `inputToLatch`
-/
section inputToLatch
variable {idx : InputIdx} {next : Lit} {reset : Option Lit}
variable (valid : idx.validIn aig) (varValid : (idx.getVar aig valid).validIn aig)

@[simp, grind .]
theorem InputsValid_inputToLatch
    (inputsValid : aig.InputsValid) :
    (aig.inputToLatch idx next reset valid varValid).fst.InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_inputToLatch
    (inputIdxsValid : aig.InputIdxsValid) :
    (aig.inputToLatch idx next reset valid varValid).fst.InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_inputToLatch
    (latchesValid : aig.LatchesValid)
    (inputsValid  : aig.InputsValid) :
    (aig.inputToLatch idx next reset valid varValid).fst.LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_inputToLatch
    (latchIdxsValid : aig.LatchIdxsValid) :
    (aig.inputToLatch idx next reset valid varValid).fst.LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_inputToLatch_none
    (resetsValid : aig.ResetsValid) :
    (aig.inputToLatch idx next none valid varValid).fst.ResetsValid := by
  grind

@[simp]
theorem ResetsValid_inputToLatch_some {reset : Lit}
    (resetsValid : aig.ResetsValid)
    (resetValid : reset.validIn aig) :
    (aig.inputToLatch idx next reset valid varValid).fst.ResetsValid := by
  grind

@[grind .]
theorem ResetsValid_inputToLatch
    (resetsValid : aig.ResetsValid)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.validIn aig) :
    (aig.inputToLatch idx next reset valid varValid).fst.ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_inputToLatch
    (nextsValid : aig.NextsValid)
    (nextValid : next.validIn aig) :
    (aig.inputToLatch idx next reset valid varValid).fst.NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_inputToLatch
    (acyclicGates : aig.AcyclicGates) :
    (aig.inputToLatch idx next reset valid varValid).fst.AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_inputToLatch_none
    (acyclicResets : aig.AcyclicResets) :
    (aig.inputToLatch idx next none valid varValid).fst.AcyclicResets := by
  grind

@[simp]
theorem AcyclicResets_inputToLatch_some {reset : Lit}
    (acyclicResets : aig.AcyclicResets)
    (resetAcyclic : reset.var < idx.getVar aig) :
    (aig.inputToLatch idx next reset valid varValid).fst.AcyclicResets := by
  grind

@[grind .]
theorem AcyclicResets_inputToLatch
    (acyclicResets : aig.AcyclicResets)
    (resetAcyclic :
      match reset with
      | none => True
      | some lit => lit.var < idx.getVar aig) :
    (aig.inputToLatch idx next reset valid varValid).fst.AcyclicResets := by
  grind

@[simp]
theorem inputToLatch_none
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig) :
    (aig.inputToLatch idx next none valid varValid).fst.WF := by
  grind

@[simp]
theorem inputToLatch_some {reset : Lit}
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig)
    (resetAcyclic : reset.var < idx.getVar aig) :
    (aig.inputToLatch idx next reset valid varValid).fst.WF := by
  grind

@[grind .]
theorem inputToLatch
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig)
    (resetAcyclic :
      match reset with
      | none => True
      | some lit => lit.var < idx.getVar aig) :
    (aig.inputToLatch idx next reset valid varValid).fst.WF := by
  grind

end inputToLatch

/-
  `inputToAnd`
-/
section inputToAnd
variable {idx : InputIdx} {lhs rhs : Lit}
variable (valid : idx.validIn aig) (varValid : (idx.getVar aig valid).validIn aig)

@[simp, grind .]
theorem InputsValid_inputToAnd
    (inputsValid : aig.InputsValid)
    (h0 : lhs.var ≠ idx.getVar aig)
    (h0 : rhs.var ≠ idx.getVar aig) :
    (aig.inputToAnd idx lhs rhs valid varValid).InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_inputToAnd
    (inputIdxsValid : aig.InputIdxsValid)
    (h0 : lhs.var ≠ idx.getVar aig)
    (h0 : rhs.var ≠ idx.getVar aig) :
    (aig.inputToAnd idx lhs rhs valid varValid).InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_inputToAnd
    (latchesValid : aig.LatchesValid)
    (inputsValid  : aig.InputsValid)
    (h0 : lhs.var ≠ idx.getVar aig)
    (h0 : rhs.var ≠ idx.getVar aig) :
    (aig.inputToAnd idx lhs rhs valid varValid).LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_inputToAnd
    (latchIdxsValid : aig.LatchIdxsValid)
    (h0 : lhs.var ≠ idx.getVar aig)
    (h0 : rhs.var ≠ idx.getVar aig) :
    (aig.inputToAnd idx lhs rhs valid varValid).LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_inputToAnd
    (resetsValid : aig.ResetsValid)
    (h0 : lhs.var ≠ idx.getVar aig)
    (h0 : rhs.var ≠ idx.getVar aig) :
    (aig.inputToAnd idx lhs rhs valid varValid).ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_inputToAnd
    (nextsValid : aig.NextsValid)
    (h0 : lhs.var ≠ idx.getVar aig)
    (h0 : rhs.var ≠ idx.getVar aig) :
    (aig.inputToAnd idx lhs rhs valid varValid).NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_inputToAnd
    (acyclicGates : aig.AcyclicGates)
    (h0 : lhs.var < idx.getVar aig)
    (h0 : rhs.var < idx.getVar aig) :
    (aig.inputToAnd idx lhs rhs valid varValid).AcyclicGates := by
  have : lhs.var ≠ idx.getVar aig ∧ rhs.var ≠ idx.getVar aig := by grind
  grind

@[simp, grind .]
theorem AcyclicResets_inputToAnd
    (acyclicResets : aig.AcyclicResets) :
    (aig.inputToAnd idx lhs rhs valid varValid).AcyclicResets := by
  grind

@[simp, grind .]
theorem inputToAnd
    (wellFormed : aig.WF)
    (h0 : lhs.var < idx.getVar aig)
    (h0 : rhs.var < idx.getVar aig) :
    (aig.inputToAnd idx lhs rhs valid varValid).WF := by
  have : lhs.var ≠ idx.getVar aig ∧ rhs.var ≠ idx.getVar aig := by grind
  grind

end inputToAnd

/-
  `changeInputIdx`
-/
section changeInputIdx
variable {old new : InputIdx}
variable (valid : old.validIn aig) (varValid : (old.getVar aig).validIn aig) (unused : ¬new.validIn aig ∨ old = new)

@[simp, grind .]
theorem InputsValid_changeInputIdx
    (inputsValid : aig.InputsValid) :
    (aig.changeInputIdx old new valid varValid unused).InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_changeInputIdx
    (inputIdxsValid : aig.InputIdxsValid) :
    (aig.changeInputIdx old new valid varValid unused).InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_changeInputIdx
    (latchesValid : aig.LatchesValid)
    (inputsValid : aig.InputsValid) :
    (aig.changeInputIdx old new valid varValid unused).LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_changeInputIdx
    (latchIdxsValid : aig.LatchIdxsValid) :
    (aig.changeInputIdx old new valid varValid unused).LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_changeInputIdx
    (resetsValid : aig.ResetsValid) :
    (aig.changeInputIdx old new valid varValid unused).ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_changeInputIdx
    (nextsValid : aig.NextsValid) :
    (aig.changeInputIdx old new valid varValid unused).NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_changeInputIdx
    (acyclicGates : aig.AcyclicGates) :
    (aig.changeInputIdx old new valid varValid unused).AcyclicGates := by
  grind

@[simp, grind .]
theorem AcyclicResets_changeInputIdx
    (acyclicResets : aig.AcyclicResets) :
    (aig.changeInputIdx old new valid varValid unused).AcyclicResets := by
  grind

@[simp, grind .]
theorem changeInputIdx
    (wellFormed : aig.WF) :
    (aig.changeInputIdx old new valid varValid unused).WF := by
  grind

end changeInputIdx

/-
  `convertToInput`
-/
section latchToInput
variable {idx : LatchIdx}
variable (valid : idx.validIn aig) (varValid : (idx.getVar aig valid).validIn aig)

@[simp, grind .]
theorem InputsValid_latchToInput
    (inputsValid : aig.InputsValid)
    (latchesValid : aig.LatchesValid) :
    (aig.latchToInput idx valid varValid).fst.InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_latchToInput
    (inputIdxsValid : aig.InputIdxsValid) :
    (aig.latchToInput idx valid varValid).fst.InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_latchToInput
    (latchesValid : aig.LatchesValid) :
    (aig.latchToInput idx valid varValid).fst.LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_latchToInput
    (latchIdxsValid : aig.LatchIdxsValid) :
    (aig.latchToInput idx valid varValid).fst.LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_latchToInput
    (resetsValid : aig.ResetsValid) :
    (aig.latchToInput idx valid varValid).fst.ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_latchToInput
    (nextsValid : aig.NextsValid) :
    (aig.latchToInput idx valid varValid).fst.NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_latchToInput
    (acyclicGates : aig.AcyclicGates) :
    (aig.latchToInput idx valid varValid).fst.AcyclicGates := by
  grind

@[simp, grind .]
theorem AcyclicResets_latchToInput
    (acyclicResets : aig.AcyclicResets) :
    (aig.latchToInput idx valid varValid).fst.AcyclicResets := by
  grind

@[simp, grind .]
theorem latchToInput
    (wellFormed : aig.WF) :
    (aig.latchToInput idx valid varValid).fst.WF := by
  grind

end latchToInput

/-
  `convertToAnd`
-/
section latchToAnd
variable {idx : LatchIdx} {lhs rhs : Lit}
variable (valid : idx.validIn aig) (varValid : (idx.getVar aig valid).validIn aig)

@[simp, grind .]
theorem InputsValid_latchToAnd
    (inputsValid : aig.InputsValid)
    (latchesValid : aig.LatchesValid)
    (h0 : lhs.var ≠ idx.getVar aig)
    (h0 : rhs.var ≠ idx.getVar aig) :
    (aig.latchToAnd idx lhs rhs valid varValid).InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_latchToAnd
    (inputIdxsValid : aig.InputIdxsValid)
    (h0 : lhs.var ≠ idx.getVar aig)
    (h0 : rhs.var ≠ idx.getVar aig) :
    (aig.latchToAnd idx lhs rhs valid varValid).InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_latchToAnd
    (latchesValid : aig.LatchesValid)
    (h0 : lhs.var ≠ idx.getVar aig)
    (h0 : rhs.var ≠ idx.getVar aig) :
    (aig.latchToAnd idx lhs rhs valid varValid).LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_latchToAnd
    (latchIdxsValid : aig.LatchIdxsValid)
    (h0 : lhs.var ≠ idx.getVar aig)
    (h0 : rhs.var ≠ idx.getVar aig) :
    (aig.latchToAnd idx lhs rhs valid varValid).LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_latchToAnd
    (resetsValid : aig.ResetsValid)
    (h0 : lhs.var ≠ idx.getVar aig)
    (h0 : rhs.var ≠ idx.getVar aig) :
    (aig.latchToAnd idx lhs rhs valid varValid).ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_latchToAnd
    (nextsValid : aig.NextsValid)
    (h0 : lhs.var ≠ idx.getVar aig)
    (h0 : rhs.var ≠ idx.getVar aig) :
    (aig.latchToAnd idx lhs rhs valid varValid).NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_latchToAnd
    (acyclicGates : aig.AcyclicGates)
    (h0 : lhs.var < idx.getVar aig)
    (h0 : rhs.var < idx.getVar aig) :
    (aig.latchToAnd idx lhs rhs valid varValid).AcyclicGates := by
  have : lhs.var ≠ idx.getVar aig ∧ rhs.var ≠ idx.getVar aig := by grind
  grind

@[simp, grind .]
theorem AcyclicResets_latchToAnd
    (acyclicResets : aig.AcyclicResets) :
    (aig.latchToAnd idx lhs rhs valid varValid).AcyclicResets := by
  grind

@[simp, grind .]
theorem latchToAnd
    (wellFormed : aig.WF)
    (h0 : lhs.var < idx.getVar aig)
    (h0 : rhs.var < idx.getVar aig) :
    (aig.latchToAnd idx lhs rhs valid varValid).WF := by
  have : lhs.var ≠ idx.getVar aig ∧ rhs.var ≠ idx.getVar aig := by grind
  grind

end latchToAnd

/-
  `changeLatchIdx`
-/
section changeLatchIdx
variable {old new : LatchIdx}
variable (valid : old.validIn aig) (varValid : (old.getVar aig).validIn aig) (unused : ¬new.validIn aig ∨ old = new)

@[simp, grind .]
theorem InputsValid_changeLatchIdx
    (inputsValid : aig.InputsValid)
    (latchesValid : aig.LatchesValid) :
    (aig.changeLatchIdx old new valid varValid unused).InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_changeLatchIdx
    (inputIdxsValid : aig.InputIdxsValid) :
    (aig.changeLatchIdx old new valid varValid unused).InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_changeLatchIdx
    (latchesValid : aig.LatchesValid) :
    (aig.changeLatchIdx old new valid varValid unused).LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_changeLatchIdx
    (latchIdxsValid : aig.LatchIdxsValid) :
    (aig.changeLatchIdx old new valid varValid unused).LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_changeLatchIdx
    (resetsValid : aig.ResetsValid) :
    (aig.changeLatchIdx old new valid varValid unused).ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_changeLatchIdx
    (nextsValid : aig.NextsValid) :
    (aig.changeLatchIdx old new valid varValid unused).NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_changeLatchIdx
    (acyclicGates : aig.AcyclicGates) :
    (aig.changeLatchIdx old new valid varValid unused).AcyclicGates := by
  grind

@[simp, grind .]
theorem AcyclicResets_changeLatchIdx
    (acyclicResets : aig.AcyclicResets) :
    (aig.changeLatchIdx old new valid varValid unused).AcyclicResets := by
  grind

@[simp, grind .]
theorem changeLatchIdx
    (wellFormed : aig.WF) :
    (aig.changeLatchIdx old new valid varValid unused).WF := by
  grind

end changeLatchIdx

/-
  `andToInput`
-/
section andToInput
variable {var : Var} (valid : var.validIn aig)

@[simp, grind .]
theorem InputsValid_andToInput isAnd
    (inputsValid : aig.InputsValid) :
    (aig.andToInput var valid isAnd).fst.InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_andToInput isAnd
    (inputIdxsValid : aig.InputIdxsValid) :
    (aig.andToInput var valid isAnd).fst.InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_andToInput isAnd
    (latchesValid : aig.LatchesValid) :
    (aig.andToInput var valid isAnd).fst.LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_andToInput isAnd
    (latchIdxsValid : aig.LatchIdxsValid) :
    (aig.andToInput var valid isAnd).fst.LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_andToInput isAnd
    (resetsValid : aig.ResetsValid) :
    (aig.andToInput var valid isAnd).fst.ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_andToInput isAnd
    (nextsValid : aig.NextsValid) :
    (aig.andToInput var valid isAnd).fst.NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_andToInput isAnd
    (acyclicGates : aig.AcyclicGates) :
    (aig.andToInput var valid isAnd).fst.AcyclicGates := by
  grind

@[simp, grind .]
theorem AcyclicResets_andToInput isAnd
    (acyclicResets : aig.AcyclicResets) :
    (aig.andToInput var valid isAnd).fst.AcyclicResets := by
  grind

@[simp, grind .]
theorem andToInput isAnd
    (wellFormed : aig.WF) :
    (aig.andToInput var valid isAnd).fst.WF := by
  grind

end andToInput

/-
  `andToLatch`
-/
section andToLatch
variable {var : Var} {next : Lit} {reset : Option Lit} (valid : var.validIn aig)

@[simp, grind .]
theorem InputsValid_andToLatch isAnd
    (inputsValid : aig.InputsValid) :
    (aig.andToLatch var next reset valid isAnd).fst.InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_andToLatch isAnd
    (inputIdxsValid : aig.InputIdxsValid) :
    (aig.andToLatch var next reset valid isAnd).fst.InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_andToLatch isAnd
    (latchesValid : aig.LatchesValid) :
    (aig.andToLatch var next reset valid isAnd).fst.LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_andToLatch isAnd
    (latchIdxsValid : aig.LatchIdxsValid) :
    (aig.andToLatch var next reset valid isAnd).fst.LatchIdxsValid := by
  grind

@[simp]
theorem ResetsValid_andToLatch_none isAnd
    (resetsValid : aig.ResetsValid) :
    (aig.andToLatch var next none valid isAnd).fst.ResetsValid := by
  grind

@[simp]
theorem ResetsValid_andToLatch_some isAnd {reset : Lit}
    (resetsValid : aig.ResetsValid)
    (resetValid : reset.validIn aig) :
    (aig.andToLatch var next reset valid isAnd).fst.ResetsValid := by
  grind

@[grind .]
theorem ResetsValid_andToLatch isAnd
    (resetsValid : aig.ResetsValid)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.validIn aig) :
    (aig.andToLatch var next reset valid isAnd).fst.ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_andToLatch isAnd
    (nextsValid : aig.NextsValid)
    (nextValid : next.validIn aig) :
    (aig.andToLatch var next reset valid isAnd).fst.NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_andToLatch isAnd
    (acyclicGates : aig.AcyclicGates) :
    (aig.andToLatch var next reset valid isAnd).fst.AcyclicGates := by
  grind

@[simp]
theorem AcyclicResets_andToLatch_none isAnd
    (acyclicResets : aig.AcyclicResets) :
    (aig.andToLatch var next none valid isAnd).fst.AcyclicResets := by
  grind

@[simp]
theorem AcyclicResets_andToLatch_some isAnd {reset : Lit}
    (acyclicResets : aig.AcyclicResets)
    (resetAcyclic : reset.var < var) :
    (aig.andToLatch var next reset valid isAnd).fst.AcyclicResets := by
  grind

@[grind .]
theorem AcyclicResets_andToLatch isAnd
    (acyclicResets : aig.AcyclicResets)
    (resetAcyclic :
      match reset with
      | none => True
      | some lit => lit.var < var) :
    (aig.andToLatch var next reset valid isAnd).fst.AcyclicResets := by
  grind

@[simp]
theorem andToLatch_none isAnd
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig) :
    (aig.andToLatch var next none valid isAnd).fst.WF := by
  grind

@[simp]
theorem andToLatch_some isAnd {reset : Lit}
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig)
    (resetAcyclic : reset.var < var) :
    (aig.andToLatch var next reset valid isAnd).fst.WF := by
  grind

@[grind .]
theorem andToLatch isAnd
    (wellFormed : aig.WF)
    (nextValid : next.validIn aig)
    (resetAcyclic :
      match reset with
      | none => True
      | some lit => lit.var < var) :
    (aig.andToLatch var next reset valid isAnd).fst.WF := by
  grind

end andToLatch

/-
  `rewriteAnd`
-/
section rewriteAnd
variable {var : Var} {lhs rhs : Lit} (valid : var.validIn aig)

@[simp, grind .]
theorem InputsValid_rewriteAnd isAnd
    (inputsValid : aig.InputsValid)
    (h0 : lhs.var ≠ var)
    (h0 : rhs.var ≠ var) :
    (aig.rewriteAnd var lhs rhs valid isAnd).InputsValid := by
  grind

@[simp, grind .]
theorem InputIdxsValid_rewriteAnd isAnd
    (inputIdxsValid : aig.InputIdxsValid)
    (h0 : lhs.var ≠ var)
    (h0 : rhs.var ≠ var) :
    (aig.rewriteAnd var lhs rhs valid isAnd).InputIdxsValid := by
  grind

@[simp, grind .]
theorem LatchesValid_rewriteAnd isAnd
    (latchesValid : aig.LatchesValid)
    (h0 : lhs.var ≠ var)
    (h0 : rhs.var ≠ var) :
    (aig.rewriteAnd var lhs rhs valid isAnd).LatchesValid := by
  grind

@[simp, grind .]
theorem LatchIdxsValid_rewriteAnd isAnd
    (latchIdxsValid : aig.LatchIdxsValid)
    (h0 : lhs.var ≠ var)
    (h0 : rhs.var ≠ var) :
    (aig.rewriteAnd var lhs rhs valid isAnd).LatchIdxsValid := by
  grind

@[simp, grind .]
theorem ResetsValid_rewriteAnd isAnd
    (resetsValid : aig.ResetsValid)
    (h0 : lhs.var ≠ var)
    (h0 : rhs.var ≠ var) :
    (aig.rewriteAnd var lhs rhs valid isAnd).ResetsValid := by
  grind

@[simp, grind .]
theorem NextsValid_rewriteAnd isAnd
    (nextsValid : aig.NextsValid)
    (h0 : lhs.var ≠ var)
    (h0 : rhs.var ≠ var) :
    (aig.rewriteAnd var lhs rhs valid isAnd).NextsValid := by
  grind

@[simp, grind .]
theorem AcyclicGates_rewriteAnd isAnd
    (acyclicGates : aig.AcyclicGates)
    (h0 : lhs.var < var)
    (h0 : rhs.var < var) :
    (aig.rewriteAnd var lhs rhs valid isAnd).AcyclicGates := by
  have : lhs.var ≠ var ∧ rhs.var ≠ var := by grind
  grind

@[simp, grind .]
theorem AcyclicResets_rewriteAnd isAnd
    (acyclicResets : aig.AcyclicResets) :
    (aig.rewriteAnd var lhs rhs valid isAnd).AcyclicResets := by
  grind

@[simp, grind .]
theorem rewriteAnd isAnd
    (wellFormed : aig.WF)
    (h0 : lhs.var < var)
    (h0 : rhs.var < var) :
    (aig.rewriteAnd var lhs rhs valid isAnd).WF := by
  have : lhs.var ≠ var ∧ rhs.var ≠ var := by grind
  grind

end rewriteAnd

end WF

end Valaig.Aig
