import Valaig.Aig.Basic

namespace Valaig.Aig

variable {aig : Aig} {var : Var}

theorem nextInputIdx_notIn_decls (aig : Aig) {i : Nat} (h : i < aig.size) :
    aig.aig.decls[i] ≠ .atom (.input aig.nextInputIdx) := by
  intro heq
  have := aig.hinputs.hsurjec h (iarr := aig.nextInputIdx) heq
  grind only [nextInputIdx]

theorem nextLatchIdx_notIn_decls (aig : Aig) {i : Nat} (h : i < aig.size) :
    aig.aig.decls[i] ≠ .atom (.latch aig.nextLatchIdx) := by
  intro heq
  have := aig.hlatches.hsurjec h (iarr := aig.nextLatchIdx) heq
  grind only [nextLatchIdx]


theorem decls_unique_inputs :
    ∀ {i j} (hi : i < aig.size) (hj : j < aig.size),
      aig.aig.decls[i] matches .atom (.input _) ∧ aig.aig.decls[i] = aig.aig.decls[j] →
      i = j := by
  grind

theorem decls_unique_latches :
    ∀ {i j} (hi : i < aig.size) (hj : j < aig.size),
      aig.aig.decls[i] matches .atom (.latch _) ∧ aig.aig.decls[i] = aig.aig.decls[j] →
      i = j := by
  grind

theorem decls_unique_atoms :
    ∀ {i j} (hi : i < aig.size) (hj : j < aig.size),
      aig.aig.decls[i] matches .atom _ ∧ aig.aig.decls[i] = aig.aig.decls[j] →
      i = j := by
  intro i j hi hj
  match h : aig.aig.decls[i] with
  | .false => simp
  | .gate _ _ => simp
  | .atom (.input _) => grind only [decls_unique_inputs]
  | .atom (.latch _) => grind only [decls_unique_latches]

theorem inputs_unique :
    ∀ {i j} (hi : i < aig.numInputs) (hj : j < aig.numInputs),
      aig.inputs[i].var = aig.inputs[j].var → i = j := by
  grind

theorem latches_unique :
    ∀ {i j} (hi : i < aig.numLatches) (hj : j < aig.numLatches),
      aig.latches[i].var = aig.latches[j].var → i = j := by
  grind

@[simp, grind! .]
theorem empty_inputs :
    empty.inputs = #[] := by
  simp only [empty]

@[simp, grind! .]
theorem empty_latches :
    empty.latches = #[] := by
  simp only [empty]

section

attribute [local simp] mkAtom_eq_decls_push
attribute [local simp] mkAtom_ref_eq_decls_size
attribute [local simp] Std.Sat.AIG.mkAtom_le_size
attribute [local simp] Std.Sat.AIG.mkAndCached_le_size

variable {symbol : String}
variable {rhs0 rhs1 : Lit} {h0 : rhs0.validIn aig} {h1 : rhs1.validIn aig}
variable {next : Lit} {reset : Option Lit}

@[grind! .]
theorem Var.constant_validIn : Var.constant.validIn aig := by
  simp [Var.validIn, Var.constant, aig.aig.hzero]

@[grind! .]
theorem Lit.validIn_mk_validIn (h : var.validIn aig) {invert : Bool} :
    Lit.mk var invert |>.validIn aig := by
  simp_all [Var.validIn]


theorem addInput_size_ge :
    (aig.addInput symbol).fst.size ≥ aig.size := by
  simp [addInput]

@[grind! .]
theorem validIn_addInput (h : var.validIn aig) :
    var.validIn (aig.addInput symbol).fst := by
  grind [addInput_size_ge, Var.validIn]

@[grind! .]
theorem addInput_validIn :
    (aig.addInput symbol).snd.var.validIn (aig.addInput symbol).fst := by
  simp [addInput, Var.validIn]

theorem addInput_inputs_eq_push :
    let (aig', input) := aig.addInput symbol
    aig'.inputs = aig.inputs.push input := by
  simp [addInput]

@[grind! .]
theorem addInput_latches_eq :
    (aig.addInput symbol).fst.latches = aig.latches := by
  simp [addInput]


theorem addLatch_size_ge :
    (aig.addLatch next reset symbol).fst.size ≥ aig.size := by
  simp [addLatch]

@[grind! .]
theorem validIn_addLatch (h : var.validIn aig) :
    var.validIn (aig.addLatch next reset symbol).fst := by
  grind [addLatch_size_ge, Var.validIn]

@[grind! .]
theorem addLatch_validIn:
    (aig.addLatch next reset symbol).snd.var.validIn (aig.addLatch next reset symbol).fst := by
  simp [addLatch, Var.validIn]

theorem addLatch_latches_eq_push :
    let (aig', latch) := aig.addLatch next reset symbol
    aig'.latches = aig.latches.push latch := by
  simp [addLatch]

@[grind! .]
theorem addLatch_inputs_eq :
    (aig.addLatch next reset symbol).fst.inputs = aig.inputs := by
  simp [addLatch]


theorem addLatch'_size_ge :
    (aig.addLatch' reset symbol).fst.size ≥ aig.size := by
  simp [addLatch']

@[grind! .]
theorem validIn_addLatch' (h : var.validIn aig) :
    var.validIn (aig.addLatch' reset symbol).fst := by
  grind [addLatch'_size_ge, Var.validIn]

@[grind! .]
theorem addLatch'_validIn:
    (aig.addLatch' reset symbol).snd.var.validIn (aig.addLatch' reset symbol).fst := by
  simp [addLatch', Var.validIn]

theorem addLatch'_latches_eq_push :
    let (aig', latch) := aig.addLatch' reset symbol
    aig'.latches = aig.latches.push latch := by
  simp [addLatch']

@[grind! .]
theorem addLatch'_inputs_eq :
    (aig.addLatch' reset symbol).fst.inputs = aig.inputs := by
  simp [addLatch']


theorem addGate_size_ge :
    (aig.addGate rhs0 rhs1 h0 h1).fst.size ≥ aig.size := by
  simp [addGate]

@[grind! .]
theorem validIn_addGate (h : var.validIn aig) :
    var.validIn (aig.addGate rhs0 rhs1 h0 h1).fst := by
  grind [addGate_size_ge, Var.validIn]

@[grind! .]
theorem addGate_validIn:
    (aig.addGate rhs0 rhs1 h0 h1).snd.validIn (aig.addGate rhs0 rhs1 h0 h1).fst := by
  simp [addGate, Var.validIn]
  have (r : Std.Sat.AIG.Entrypoint Aig.Atom) := r.ref.hgate
  grind

@[grind! .]
theorem addGate_inputs_eq :
    (aig.addGate rhs0 rhs1 h0 h1).fst.inputs = aig.inputs := by
  simp [addGate]

@[grind! .]
theorem addGate_latches_eq :
    (aig.addGate rhs0 rhs1 h0 h1).fst.latches = aig.latches := by
  simp [addGate]

end

section

variable {nextState : (latch : Latch) -> latch ∈ aig.latches -> Lit.In aig}
variable {state : FinaliseLatchesState aig}

theorem finaliseLatches.updateLatches_size_const :
    let state' := (finaliseLatches.updateLatches aig nextState (s := state))
    state'.latches.size = state.latches.size := by
  intro state'
  simp_all only [state.hsize, state'.hsize]

theorem finaliseLatches.updateLatches_modified_once :
    let state' := (finaliseLatches.updateLatches aig nextState (s := state))
    ∀ {i} (_ : i < state'.latches.size) (_ : i < state.idx),
      state'.latches[i] = state.latches[i]'(by grind [updateLatches_size_const]) := by
  induction h : (state.latches.size - state.idx) generalizing state with
  | zero => grind only [updateLatches]
  | succ n' ih =>
    dsimp only
    intro i h1 h2
    by_cases i ≠ state.idx
    · by_cases state.latches[state.idx].next.isSome
      · grind only [updateLatches, hlatches, updateLatches_size_const, Option.isSome_none]
      · grind only [updateLatches, Array.size_modify, hlatches, Array.getElem_modify]
    · grind only [updateLatches]

theorem finaliseLatches.updateLatches_next_eq_some :
    let state' := (finaliseLatches.updateLatches aig nextState (s := state))
    ∀ {i} (_ : i < state'.latches.size) (_ : i ≥ state.idx),
      state'.latches[i].next.isSome := by
  induction h : (state.latches.size - state.idx) generalizing state with
  | zero => grind only [updateLatches]
  | succ n' ih =>
    grind only [updateLatches, hlatches, updateLatches_modified_once, Option.isSome_some, Array.getElem_modify]

theorem finaliseLatches_WF :
    aig.finaliseLatches nextState |>.WF := by
  constructor
  · simp only [finaliseLatches]
    grind [Array.mem_def, List.mem_iff_getElem, finaliseLatches.updateLatches_next_eq_some]

theorem finaliseLatches_aig_eq :
    (aig.finaliseLatches nextState).aig = aig.aig := by
  simp only [finaliseLatches]

@[grind! .]
theorem validIn_finaliseLatches (h : var.validIn aig) :
    var.validIn (aig.finaliseLatches nextState) := by
  simp_all only [Var.validIn, Raw.size, finaliseLatches_aig_eq]

end

end Valaig.Aig
