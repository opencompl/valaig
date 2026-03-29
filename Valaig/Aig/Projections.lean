module

import all Valaig.Aig.Basic
public import Valaig.Aig.Semantics
public import Valaig.Aig.Iter

namespace Valaig.Aig
variable {aig : Aig} {wf : aig.WellFormed}

namespace resetAig

@[always_inline]
def step (aig : Aig) (state : Aig) (map : Array Lit) (var : Var)
    (valid : var.validIn aig := by grind)
    (wf : aig.WellFormed := by grind)
    (valid : ∀ lit ∈ map, lit.validIn state := by grind)
    (size : var.idx = map.size := by grind) :
    Aig × Array Lit :=
  let mapLit (lit : Lit) (h : lit.var < var := by grind) : Lit.In state :=
    lit.mapTo map[lit.var.idx] |>.castIn state

  let (eq:=_) (state, lit) : Aig × Lit :=
    match _ : aig[var] with
    | .false         => (state, .false)
    | .input idx     => let state := state.addInput' idx
                        (state, idx.getLit state)
    | .latch idx     =>
      match _ : idx.getReset aig with
      | none         => let state := state.addLatch' idx .false none
                        (state, idx.getLit state)
      | some reset   => (state, mapLit reset)
    | .and rhs0 rhs1 => state.addAnd (mapLit rhs0) (mapLit rhs1)

  (state, map.push lit)

variable {state : Aig} {map : Array Lit} {var : Var}
variable {valid : var.validIn aig}
variable {wf : aig.WellFormed}
variable {swf : state.WellFormed}
variable {valid : ∀ lit ∈ map, lit.validIn state}
variable {size : var.idx = map.size}
variable {inputInvalid : ∀ {idx}, aig[var] = .input idx → ¬idx.validIn state}
variable {latchInvalid : ∀ {idx}, aig[var] = .latch idx → ¬idx.validIn state}

@[simp, grind =]
theorem size_step :
    (step aig state map var).snd.size = map.size + 1 := by
  unfold step
  grind

@[simp, grind .]
theorem input_validIn_step {idx : InputIdx} (valid : idx.validIn aig)
    (h : (idx.getVar aig < var ∧ idx.validIn state) ∨ idx.getVar aig = var) :
    idx.validIn (step aig state map var).fst := by
  unfold step
  grind

@[simp, grind .]
theorem inputs_not_validIn_step {idx : InputIdx} (valid : idx.validIn aig) (invalid : ¬idx.validIn state)
    (gt : idx.getVar aig > var) :
    ¬idx.validIn (step aig state map var).fst := by
  unfold step
  grind

@[simp, grind .]
theorem latch_validIn_step {idx : LatchIdx} (valid : idx.validIn aig)
    (h : (idx.getVar aig < var ∧ idx.validIn state) ∨ (idx.getVar aig = var ∧ idx.getReset aig = none)) :
    idx.validIn (step aig state map var).fst := by
  unfold step
  grind

@[simp, grind .]
theorem latches_not_validIn_step {idx : LatchIdx} (valid : idx.validIn aig) (invalid : ¬idx.validIn state)
    (gt : idx.getVar aig > var) :
    ¬idx.validIn (step aig state map var).fst := by
  unfold step
  grind

include inputInvalid latchInvalid swf in
@[simp, grind .]
theorem WellFormed_step :
    (step aig state map var).fst.WellFormed := by
  unfold step
  grind

include inputInvalid in
@[simp, grind .]
theorem valid_step {lit : Lit}
   (h : lit ∈ (step aig state map var).snd) :
    lit.validIn (step aig state map var).fst := by
  simp_all only [step]
  grind

end resetAig

/--
Construct a new Aig representing the values of nodes in the first cycle, assigning each
latch its reset value. This results in a combinational Aig with the same number of inputs
and a map to map from literals in the old Aig to the new one.
-/
def resetAig (aig : Aig) (wf : aig.WellFormed := by grind) : Aig × (Lit.In aig -> Lit) :=
  go aig.iter .empty (.emptyWithCapacity aig.size)
where
  go it state (map : Array Lit)
      (wf : state.WellFormed := by grind)
      (valid : ∀ lit ∈ map, lit.validIn state := by grind)
      (inputsInvalid : ∀ {var : Var} {idx h},
        aig[var]'h = .input idx -> var ≥ aig.iterVal it → ¬idx.validIn state := by grind)
      (latchesInvalid : ∀ {var : Var} {idx h},
        aig[var]'h = .latch idx -> var ≥ aig.iterVal it → ¬idx.validIn state := by grind)
      (size : (aig.iterVal it).idx = map.size := by grind) :=
    match it.step with
    | .done _ =>
      ⟨state, fun lit => lit.val.mapTo <| map[lit.val.var.idx]'(by grind [Var.validIn_iff])⟩
    | .yield it' var _ =>
      let (eq:=_) res := resetAig.step aig state map var
      go it' res.fst res.snd
  termination_by it.finitelyManySteps

@[simp, grind .]
theorem WellFormed_resetAig :
    aig.resetAig.fst.WellFormed := by
  grind [resetAig, @WellFormed_go]
where
  WellFormed_go {a b c d e f g h} :
      (resetAig.go aig wf a b c d e f g h).fst.WellFormed := by
    fun_induction resetAig.go <;> grind

@[simp, grind =]
theorem input_validIn_resetAig {idx : InputIdx} :
    idx.validIn aig.resetAig.fst ↔ idx.validIn aig := by
  grind [resetAig, @input_validIn_go]
where
  input_validIn_go {it state a b c d e f} :
      let res := resetAig.go aig wf it state a b c d e f
      idx.validIn res.fst ↔
      idx.validIn state ∨ ∃ h, idx.getVar aig h ≥ (aig.iterVal it) := by
    fun_induction resetAig.go <;> grind [resetAig.step]

@[simp, grind =]
theorem numInputs_resetAig :
    aig.resetAig.fst.numInputs = aig.numInputs := by
  grind [numInputs_eq_of_validIn_eq]

@[simp, grind .]
theorem resetAig_validIn {lit : Lit.In aig} :
    (aig.resetAig.snd lit).validIn aig.resetAig.fst := by
  grind [resetAig, @go_validIn]
where
  go_validIn {a b c d e f g h} :
      let res := resetAig.go aig wf a b c d e f g h
      (res.snd lit).validIn res.fst := by
    fun_induction resetAig.go <;> grind

section denote_resetAig

variable {state : Aig} {map : Array Lit} {swf : state.WellFormed}
variable {denote : ∀ {assign} {var : Var} (lt : var.idx < map.size),
           state.denoteComb map[var.idx] assign = aig.denoteResetVar var assign}

include denote in
theorem denote_mapTo (lit : Lit) {lt : lit.var.idx < map.size} :
      state.denoteComb (lit.mapTo map[lit.var.idx]) assign swf = aig.denoteReset lit assign wf := by
    grind [denoteReset_eq_denoteResetVar]

include denote in
@[local grind =]
theorem denote_step {var var' a b c}
    {inputInvalid : ∀ {idx}, aig[var'] = .input idx → ¬idx.validIn state}
    {latchInvalid : ∀ {idx}, aig[var'] = .latch idx → ¬idx.validIn state} :
    let res := resetAig.step aig state map var' a wf b c
    (lt : var.idx < res.snd.size) →
      res.fst.denoteComb res.snd[var.idx] assign = aig.denoteResetVar var assign := by
  intro res h
  rw [show res.snd[var.idx] = (map.push res.snd[map.size])[var.idx] by simp [res, resetAig.step], Array.getElem_push]
  split
  · simp only [res, resetAig.step]
    grind
  · have : var = var' := by grind
    cases h : aig[var']
    <;> simp only [res, resetAig.step, Array.getElem_push_eq]
    · grind -splitMatch -splitIte
    · grind -splitMatch -splitIte
    · grind -splitIte [denote_mapTo (aig := aig)]
    · grind -splitMatch -splitIte [denote_mapTo (aig := aig)]

include denote in
theorem denote_go (lit : Lit.In aig) {it a b c d wf'} :
    let res := resetAig.go aig wf it state map swf a b c d
    res.fst.denoteComb (res.snd lit) assign wf' = aig.denoteReset lit assign := by
  fun_induction resetAig.go
  · grind only [denote_mapTo]
  next ih =>
    apply ih
    intros
    apply denote_step <;> grind

end denote_resetAig

@[simp, grind =]
theorem denote_resetAig {assign} {lit : Lit.In aig} :
    aig.resetAig.fst.denoteComb (aig.resetAig.snd lit) assign =
    aig.denoteReset lit assign wf := by
  grind [resetAig, denote_go]
