import Valaig.Aig.Basic

namespace Valaig

attribute [local grind] Aig.Raw.aig
attribute [local grind! .] Std.Sat.AIG.hzero
attribute [local grind! .] Std.Sat.AIG.hconst
attribute [local grind! .] Aig.hfalse
attribute [local grind! .] Aig.hinputs
attribute [local grind! .] Aig.hlatches

section
variable {aig : Aig.Raw}

theorem Var.validIn_def {var : Var} :
    var.validIn aig ↔ var.idx < aig.size := by
  simp_all only [Aig.Raw.size, Var.validIn]

@[simp, grind! .]
theorem Var.constant_validIn : Var.constant.validIn aig := by
  simp [Var.validIn, Var.constant, aig.aig.hzero, Aig.Raw.size]

@[simp, grind! .]
theorem Lit.validIn_mk_validIn {var : Var} (h : var.validIn aig) {invert : Bool} :
    Lit.mk var invert |>.validIn aig := by
  simp_all only [Var.validIn, Aig.Raw.size, Lit.mk_var]

end

namespace Aig

theorem getElem_def {v : Var} (h : v.validIn aig) :
    aig[v] = aig.aig.decls[v.idx] := by
  simp_all only [Raw.instGetElemVar]

attribute [local simp, local grind =] getElem_def
attribute [local simp, local grind] Raw.size
attribute [local simp, local grind .] Array.getElem_of_mem

variable {aig : Aig}

@[simp, grind =]
theorem mem_iff_getElem {a : Std.Sat.AIG.Decl AtomIdx}  :
    a ∈ aig ↔ ∃ (v : Var), ∃ (h : v.validIn aig), aig[v] = a := by
  simp only [instMem, Raw.instMem, Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, h⟩
    exists Var.ofIdx i
  · rintro ⟨v, h⟩
    exists v.idx

theorem nextInputIdx_not_mem_aig :
    .atom (.input aig.nextInputIdx) ∉ aig:= by
  simp
  intro _ h
  have := aig.hinputs.hsurjec h (iarr := aig.nextInputIdx)
  grind only [nextInputIdx]

theorem nextLatchIdx_not_mem_aig :
    .atom (.latch aig.nextLatchIdx) ∉ aig:= by
  simp
  intro _ h
  have := aig.hlatches.hsurjec h (iarr := aig.nextLatchIdx)
  grind only [nextLatchIdx]

theorem decls_unique_inputs {i j : Nat}
    (hi : i < aig.size)
    (hj : j < aig.size)
    (hatom : aig.aig.decls[i] matches .atom (.input _))
    (heq : aig.aig.decls[i] = aig.aig.decls[j]) :
    i = j := by
  have {iarr : Nat} := aig.hinputs.hsurjec hi (iarr := iarr)
  have {iarr : Nat} := aig.hinputs.hsurjec hj (iarr := iarr)
  grind only

theorem decls_unique_latches {i j : Nat}
    (hi : i < aig.size)
    (hj : j < aig.size)
    (hatom : aig.aig.decls[i] matches .atom (.latch _))
    (heq : aig.aig.decls[i] = aig.aig.decls[j]) :
    i = j := by
  have {iarr : Nat} := aig.hlatches.hsurjec hi (iarr := iarr)
  have {iarr : Nat} := aig.hlatches.hsurjec hj (iarr := iarr)
  grind only

theorem decls_unique_atoms {i j : Nat}
    (hi : i < aig.size)
    (hj : j < aig.size)
    (hatom : aig.aig.decls[i] matches .atom _)
    (heq : aig.aig.decls[i] = aig.aig.decls[j]) :
    i = j := by
  match h : aig.aig.decls[i], hatom with
  | .atom (.input _), _ => grind only [decls_unique_inputs]
  | .atom (.latch _), _ => grind only [decls_unique_latches]

theorem inputs_unique {i j : Nat} (hi : i < aig.numInputs) (hj : j < aig.numInputs)
    (heq : aig.inputs[i].var = aig.inputs[j].var) : i = j := by
  grind only [hinputs]

theorem latches_unique {i j : Nat} (hi : i < aig.numLatches) (hj : j < aig.numLatches)
    (heq : aig.latches[i].var = aig.latches[j].var) : i = j := by
  grind only [hlatches]

@[simp, grind! .]
theorem empty_inputs :
    empty.inputs = #[] := by
  simp only [empty]

@[simp, grind! .]
theorem empty_latches :
    empty.latches = #[] := by
  simp only [empty]

@[simp, grind! .]
theorem input_mem_validIn {input : Input} (hmem : input ∈ aig.inputs) :
    input.var.validIn aig := by
  grind only [Array.getElem_of_mem, hinputs, =Var.validIn_def, Raw.size]

@[simp, grind! .]
theorem latch_mem_validIn {latch : Latch} (hmem : latch ∈ aig.latches) :
    latch.var.validIn aig := by
  grind only [Array.getElem_of_mem, hlatches, =Var.validIn_def, Raw.size]

@[simp, grind! .]
theorem input_mem_matches_input {input : Input} (hmem : input ∈ aig.inputs) :
    aig[input.var]'(input_mem_validIn hmem) matches .atom (.input _) := by
  grind only [hinputs, Array.getElem_of_mem, getElem_def]

@[simp, grind! .]
theorem latch_mem_matches_latch {latch : Latch} (hmem : latch ∈ aig.latches) :
    aig[latch.var]'(latch_mem_validIn hmem) matches .atom (.latch _) := by
  grind only [!hlatches, Array.getElem_of_mem, getElem_def]

section
variable {aig : Aig} {var : Var}
variable {symbol : String}
variable {rhs0 rhs1 : Lit} {h0 : rhs0.validIn aig} {h1 : rhs1.validIn aig}
variable {next : Lit} {reset : Option Lit}

attribute [local simp] mkAtom_eq_decls_push
attribute [local simp] mkAtom_ref_eq_decls_size
attribute [local simp] Std.Sat.AIG.mkAtom_le_size
attribute [local simp] Std.Sat.AIG.mkAndCached_le_size

-- addInput Lemmas

theorem addInput_size_ge :
    (aig.addInput symbol).fst.size ≥ aig.size := by
  simp [addInput]

@[grind! .]
theorem validIn_addInput (h : var.validIn aig) :
    var.validIn (aig.addInput symbol).fst := by
  grind only [addInput_size_ge, Var.validIn_def]

@[grind! .]
theorem addInput_validIn :
    (aig.addInput symbol).snd.var.validIn (aig.addInput symbol).fst := by
  simp [addInput, Var.validIn_def]

@[simp]
theorem addInput_inputs_eq_push :
    let (aig', input) := aig.addInput symbol
    aig'.inputs = aig.inputs.push input := by
  simp [addInput]

@[grind! .]
theorem addInput_mem_inputs :
    let (aig', input) := aig.addInput symbol
    input ∈ aig'.inputs := by
  grind only [addInput_inputs_eq_push, Array.mem_push]

@[grind! .]
theorem addInput_matches_atom_input :
    let (eq:=_) (aig', input) := aig.addInput symbol
    aig'[input.var]'(by grind only [addInput_validIn]) matches .atom (.input _) := by
  apply input_mem_matches_input
  exact addInput_mem_inputs

@[grind! .]
theorem addInput_matches_atom :
    let (eq:=_) (aig', input) := aig.addInput symbol
    aig'[input.var]'(by grind only [addInput_validIn]) matches .atom _ := by
  grind only [addInput_matches_atom_input]

@[simp, grind! .]
theorem addInput_latches_eq :
    (aig.addInput symbol).fst.latches = aig.latches := by
  simp [addInput]

@[simp, grind! .]
theorem addInput_getElem_eq {var : Var} (h : var.validIn aig) :
    (aig.addInput symbol).fst[var]'(validIn_addInput h) = aig[var] := by
  rw [Var.validIn_def] at h
  simp_all [addInput, Array.getElem_push_lt]

@[grind! .]
theorem addInput_mem_eq {decl} (h : decl ∈ aig) :
    decl ∈ (aig.addInput symbol).fst := by
  rw [mem_iff_getElem] at *
  rcases h with ⟨v, ⟨h, heq⟩⟩
  exists v
  exists (validIn_addInput h)
  rw [←heq]
  apply addInput_getElem_eq

-- addLatch Lemmas

theorem addLatch_size_ge :
    (aig.addLatch next reset symbol).fst.size ≥ aig.size := by
  simp [addLatch]

@[grind! .]
theorem validIn_addLatch (h : var.validIn aig) :
    var.validIn (aig.addLatch next reset symbol).fst := by
  grind only [addLatch_size_ge, Var.validIn_def]

@[grind! .]
theorem addLatch_validIn:
    (aig.addLatch next reset symbol).snd.var.validIn (aig.addLatch next reset symbol).fst := by
  simp [addLatch, Var.validIn_def]

@[simp]
theorem addLatch_latches_eq_push :
    let (aig', latch) := aig.addLatch next reset symbol
    aig'.latches = aig.latches.push latch := by
  simp [addLatch]

@[grind! .]
theorem addLatch_mem_latches :
    let (aig', latch) := aig.addLatch next reset symbol
    latch ∈ aig'.latches := by
  grind only [addLatch_latches_eq_push, Array.mem_push]

@[grind! .]
theorem addLatch_matches_atom_latch :
    let (eq:=_) (aig', latch) := aig.addLatch next reset symbol
    aig'[latch.var]'(by grind only [addLatch_validIn]) matches .atom (.latch _) := by
  apply latch_mem_matches_latch
  exact addLatch_mem_latches

@[grind! .]
theorem addLatch_matches_atom :
    let (eq:=_) (aig', latch) := aig.addLatch next reset symbol
    aig'[latch.var]'(by grind only [addLatch_validIn]) matches .atom _ := by
  grind only [addLatch_matches_atom_latch]

@[simp, grind! .]
theorem addLatch_inputs_eq :
    (aig.addLatch next reset symbol).fst.inputs = aig.inputs := by
  simp [addLatch]

@[simp, grind! .]
theorem addLatch_getElem_eq {var : Var} (h : var.validIn aig) :
    (aig.addLatch next reset symbol).fst[var]'(validIn_addLatch h) = aig[var] := by
  rw [Var.validIn_def] at h
  simp_all [addLatch, Array.getElem_push_lt]

@[grind! .]
theorem addLatch_mem_eq {decl} (h : decl ∈ aig) :
    decl ∈ (aig.addLatch next reset symbol).fst := by
  rw [mem_iff_getElem] at *
  rcases h with ⟨v, ⟨h, heq⟩⟩
  exists v
  exists (validIn_addLatch h)
  rw [←heq]
  apply addLatch_getElem_eq

-- addLatch' Lemmas

theorem addLatch'_size_ge :
    (aig.addLatch' reset symbol).fst.size ≥ aig.size := by
  simp [addLatch']

@[grind! .]
theorem validIn_addLatch' (h : var.validIn aig) :
    var.validIn (aig.addLatch' reset symbol).fst := by
  grind only [addLatch'_size_ge, Var.validIn_def]

@[grind! .]
theorem addLatch'_validIn:
    (aig.addLatch' reset symbol).snd.var.validIn (aig.addLatch' reset symbol).fst := by
  simp [addLatch', Var.validIn_def]

@[simp]
theorem addLatch'_latches_eq_push :
    let (aig', latch) := aig.addLatch' reset symbol
    aig'.latches = aig.latches.push latch := by
  simp [addLatch']

@[grind! .]
theorem addLatch'_mem_latches :
    let (aig', latch) := aig.addLatch' reset symbol
    latch ∈ aig'.latches := by
  grind only [addLatch'_latches_eq_push, Array.mem_push]

@[grind! .]
theorem addLatch'_matches_atom_latch :
    let (eq:=_) (aig', latch) := aig.addLatch' reset symbol
    aig'[latch.var]'(by grind only [addLatch'_validIn]) matches .atom (.latch _) := by
  apply latch_mem_matches_latch
  exact addLatch'_mem_latches

@[grind! .]
theorem addLatch'_matches_atom :
    let (eq:=_) (aig', latch) := aig.addLatch' reset symbol
    aig'[latch.var]'(by grind only [addLatch'_validIn]) matches .atom _ := by
  grind only [addLatch'_matches_atom_latch]

@[simp, grind! .]
theorem addLatch'_inputs_eq :
    (aig.addLatch' reset symbol).fst.inputs = aig.inputs := by
  simp [addLatch']

@[simp, grind! .]
theorem addLatch'_getElem_eq {var : Var} (h : var.validIn aig) :
    (aig.addLatch' reset symbol).fst[var]'(validIn_addLatch' h) = aig[var] := by
  rw [Var.validIn_def] at h
  simp_all [addLatch', Array.getElem_push_lt]

@[grind! .]
theorem addLatch'_mem_eq {decl} (h : decl ∈ aig) :
    decl ∈ (aig.addLatch' reset symbol).fst := by
  rw [mem_iff_getElem] at *
  rcases h with ⟨v, ⟨h, heq⟩⟩
  exists v
  exists (validIn_addLatch' h)
  rw [←heq]
  apply addLatch'_getElem_eq

-- addGate Lemmas

theorem addGate_size_ge :
    (aig.addGate rhs0 rhs1 h0 h1).fst.size ≥ aig.size := by
  simp [addGate]

@[grind! .]
theorem validIn_addGate (h : var.validIn aig) :
    var.validIn (aig.addGate rhs0 rhs1 h0 h1).fst := by
  grind only [addGate_size_ge, Var.validIn_def]

@[grind! .]
theorem addGate_validIn:
    (aig.addGate rhs0 rhs1 h0 h1).snd.validIn (aig.addGate rhs0 rhs1 h0 h1).fst := by
  simp [addGate, Var.validIn_def]
  have (r : Std.Sat.AIG.Entrypoint Aig.AtomIdx) := r.ref.hgate
  grind only

@[simp, grind! .]
theorem addGate_inputs_eq :
    (aig.addGate rhs0 rhs1 h0 h1).fst.inputs = aig.inputs := by
  simp [addGate]

@[simp, grind! .]
theorem addGate_latches_eq :
    (aig.addGate rhs0 rhs1 h0 h1).fst.latches = aig.latches := by
  simp [addGate]

@[simp, grind! .]
theorem addGate_getElem_eq {var : Var} (h : var.validIn aig) :
    (aig.addGate rhs0 rhs1 h0 h1).fst[var]'(validIn_addGate h) = aig[var] := by
  apply Std.Sat.AIG.mkGateCached_decl_eq

@[grind! .]
theorem addGate_mem_eq {decl} (h : decl ∈ aig) :
    decl ∈ (aig.addGate rhs0 rhs1 h0 h1).fst := by
  rw [mem_iff_getElem] at *
  rcases h with ⟨v, ⟨h, heq⟩⟩
  exists v
  exists (validIn_addGate h)
  rw [←heq]
  apply addGate_getElem_eq

end

section

-- TODO: These proofs are messy

variable {nextState : (latch : Latch) -> latch ∈ aig.latches -> Lit.In aig}
variable {init state : finaliseLatches.State aig}

structure finaliseLatches.induction (nextState : (latch : Latch) -> latch ∈ aig.latches -> Lit.In aig) where
  motive (init state : State aig) : Prop
  hinit : motive (.empty aig) (.empty aig)
  htrans (init state : State aig) (hidx : state.idx ≥ init.idx) {h} :
    motive init state -> motive init (step aig nextState state h)

theorem finaliseLatches.induction.lift' (thm : induction nextState)
    (hmotive : thm.motive init state) (hidx : state.idx ≥ init.idx) :
    thm.motive init (updateLatches aig nextState (s := state)) := by
  induction h : (state.latches.size - state.idx) generalizing state with
  | zero =>
    unfold updateLatches
    grind only
  | succ n' ih =>
    unfold updateLatches
    split
    · trivial
    · simp_all
      apply ih
      · apply thm.htrans
        · exact hidx
        · exact hmotive
      · grind only [State.hsize]
      · grind only [State.hsize]

theorem finaliseLatches.induction.lift (thm : induction nextState) :
    thm.motive (.empty aig) (updateLatches aig nextState (s := .empty aig)) := by
  apply lift'
  · exact thm.hinit
  · omega

theorem finaliseLatches.updateLatches_size_const :
    let state' := (finaliseLatches.updateLatches aig nextState (s := state))
    state'.latches.size = state.latches.size := by
  intro state'
  simp_all only [state.hsize, state'.hsize]

def finaliseLatches.modified_once : induction nextState := {
  motive init state := ∀ {i} (_ : i < state.latches.size) (_ : i < init.idx),
    state.latches[i] = init.latches[i]'(by grind only [updateLatches_size_const])

  hinit := by grind only
  htrans := by
    intro init state _ _ _ i
    unfold step
    by_cases h : state.latches[state.idx].next.isSome
    · rcases Option.isSome_iff_exists.mp h with ⟨latch, heq⟩
      grind only
    · grind only [Array.getElem_modify]
}

def finaliseLatches.next_eq_some : induction nextState := {
  motive init state := 
    ∀ {i} (_ : i < state.latches.size) (_ : i < state.idx),
      state.latches[i].next.isSome

  hinit := by grind only [State.empty],

  htrans := by
    intro init state hidx h ha i hi _
    unfold step
    by_cases h : state.latches[state.idx].next.isSome
    · rcases Option.isSome_iff_exists.mp h with ⟨latch, heq⟩
      grind only
    · simp_all
      by_cases i = state.idx
      · simp_all [Array.getElem_modify_self]
      · rw [Array.getElem_modify_of_ne]
        · apply ha
          grind only
        · lia
}

theorem finaliseLatches.updateLatches_idx_eq_size_ind (h : state.idx ≤ state.latches.size) :
    let state' := (finaliseLatches.updateLatches aig nextState (s := state))
    state'.idx = state'.latches.size := by
  induction h : (state.latches.size - state.idx) generalizing state with
  | zero =>
    unfold updateLatches
    grind only
  | succ n' ih =>
    unfold updateLatches
    simp_all
    split
    · lia
    · apply ih
      · simp [State.hsize] at *
        grind
      · grind only [State.hsize]

theorem finaliseLatches.updateLatches_idx_eq_size :
    let state' := (finaliseLatches.updateLatches aig nextState)
    state'.idx = state'.latches.size := by
  apply updateLatches_idx_eq_size_ind
  · simp only [State.empty, Nat.zero_le]

theorem finaliseLatches.updateLatches_next_eq_some :
    let state' := (finaliseLatches.updateLatches aig nextState)
    ∀ {i} (_ : i < state'.latches.size), state'.latches[i].next.isSome := by
  intros
  apply next_eq_some.lift
  · grind only [updateLatches_idx_eq_size]

theorem finaliseLatches_WF :
    aig.finaliseLatches nextState |>.WF := by
  constructor
  · grind only [finaliseLatches, Array.mem_iff_getElem, finaliseLatches.updateLatches_next_eq_some]

theorem finaliseLatches_aig_eq :
    (aig.finaliseLatches nextState).aig = aig.aig := by
  simp only [finaliseLatches]

theorem finaliseLatches_inputs_eq :
    (aig.finaliseLatches nextState).inputs = aig.inputs := by
  simp only [finaliseLatches]

@[grind! .]
theorem validIn_finaliseLatches {var : Var} (h : var.validIn aig) :
    var.validIn (aig.finaliseLatches nextState) := by
  simp_all only [Var.validIn, Raw.size, finaliseLatches_aig_eq]

end

end Valaig.Aig
