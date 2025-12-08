import Valaig.Aig.Basic

namespace Valaig.Aig

variable {aig : Aig} {var : Var}

theorem decls_unique_inputs :
    ∀ {i j} (hi : i < aig.size) (hj : j < aig.size),
      aig.aig.decls[i] matches .atom (.input _) ∧ aig.aig.decls[i] = aig.aig.decls[j] →
      i = j := by
  have := aig.hinputmap.hsurjec
  grind

theorem decls_unique_latches :
    ∀ {i j} (hi : i < aig.size) (hj : j < aig.size),
      aig.aig.decls[i] matches .atom (.latch _) ∧ aig.aig.decls[i] = aig.aig.decls[j] →
      i = j := by
  have := aig.hlatchmap.hsurjec
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
theorem empty_inputs_eq_empty :
    empty.inputs = #[] := by
  simp [empty]

@[simp, grind! .]
theorem empty_latches_eq_empty :
    empty.latches = #[] := by
  simp [empty]

section

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
  have := state.hsize
  have := state'.hsize
  omega

theorem finaliseLatches.updateLatches_modified_once :
    let state' := (finaliseLatches.updateLatches aig nextState (s := state))
    ∀ {i} (_ : i < state'.latches.size) (_ : i < state.idx),
      state'.latches[i] = state.latches[i]'(by grind [finaliseLatches.updateLatches_size_const]) := by
  induction h : (state.latches.size - state.idx) generalizing state with
  | zero => grind [updateLatches]
  | succ n' ih =>
    simp only [updateLatches_size_const]
    grind [updateLatches]

theorem finaliseLatches.updateLatches_next_eq_some :
    let state' := (finaliseLatches.updateLatches aig nextState (s := state))
    ∀ {i} (_ : i < state'.latches.size) (_ : i ≥ state.idx),
      state'.latches[i].next.isSome := by
  induction h : (state.latches.size - state.idx) generalizing state with
  | zero => grind [updateLatches]
  | succ n' ih => grind [updateLatches, updateLatches_modified_once]

theorem finaliseLatches_WF :
    aig.finaliseLatches nextState |>.WF := by
  constructor
  · simp only [finaliseLatches]
    grind [finaliseLatches.updateLatches_next_eq_some, List.mem_iff_getElem, Array.mem_def]

theorem finaliseLatches_aig_eq :
    (aig.finaliseLatches nextState).aig = aig.aig := by
  simp [finaliseLatches]

@[grind! .]
theorem validIn_finaliseLatches (h : var.validIn aig) :
    var.validIn (aig.finaliseLatches nextState) := by
  simp_all [finaliseLatches_aig_eq, Var.validIn]

end

end Valaig.Aig
