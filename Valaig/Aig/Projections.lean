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
    | .latch idx     => (state, mapLit (idx.getReset aig))
    | .and rhs0 rhs1 => state.addAnd (mapLit rhs0) (mapLit rhs1)

  (state, map.push lit)

variable {state : Aig} {map : Array Lit} {var : Var}
variable {valid : var.validIn aig}
variable {wf : aig.WellFormed}
variable {swf : state.WellFormed}
variable {valid : ∀ lit ∈ map, lit.validIn state}
variable {size : var.idx = map.size}
variable {idxInvalid : ∀ {idx}, aig[var] = .input idx → ¬idx.validIn state}

@[simp, grind .]
theorem Comb_step (comb : state.Comb) :
    (step aig state map var).fst.Comb := by
  unfold step
  grind

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
theorem inputsInvalid_step {idx : InputIdx} (h : idx.validIn aig)
    (hs : (idx.getVar aig < var ∧ idx.validIn state) ∨ idx.getVar aig = var) :
    idx.validIn (step aig state map var).fst := by
  unfold step
  grind

include idxInvalid swf in
@[simp, grind .]
theorem WellFormed_step :
    (step aig state map var).fst.WellFormed := by
  unfold step
  grind

include idxInvalid in
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
      (size : (aig.iterVal it).idx = map.size := by grind) :=
    match it.step with
    | .done _ =>
      ⟨state, fun lit => lit.val.mapTo <| map[lit.val.var.idx]'(by grind [Var.validIn_iff])⟩
    | .yield it' var _ =>
      let (eq:=_) res := resetAig.step aig state map var
      go it' res.fst res.snd
  termination_by it.finitelyManySteps

@[simp, grind .]
theorem Comb_resetAig :
    aig.resetAig.fst.Comb := by
  grind [resetAig, @Comb_go]
where
  Comb_go {it state map swf inputsValid valid size} (comb : state.Comb) :
      (resetAig.go aig wf it state map swf inputsValid valid size).fst.Comb := by
    fun_induction resetAig.go <;> grind

@[simp, grind .]
theorem WellFormed_resetAig :
    aig.resetAig.fst.WellFormed := by
  grind [resetAig, @WellFormed_go]
where
  WellFormed_go {it state map swf inputsValid valid size} :
      (resetAig.go aig wf it state map swf inputsValid valid size).fst.WellFormed := by
    fun_induction resetAig.go <;> grind

@[simp, grind =]
theorem input_validIn_resetAig {idx : InputIdx} :
    idx.validIn aig.resetAig.fst ↔ idx.validIn aig := by
  grind [resetAig, @input_validIn_go]
where
  input_validIn_go {it state map swf inputsValid valid size} :
      let res := resetAig.go aig wf it state map swf inputsValid valid size
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
  go_validIn {it state map swf inputsValid valid size} :
      let res := resetAig.go aig wf it state map swf inputsValid valid size
      (res.snd lit).validIn res.fst := by
    fun_induction resetAig.go <;> grind

section denote_resetAig

variable {state : Aig} {map : Array Lit} {swf : state.WellFormed}
variable {denote : ∀ {var : Var} (lt : var.idx < map.size), state.denote map[var.idx] 0 assign = aig.denoteVar var 0 assign}

include denote in
@[local grind .]
theorem denote_mapTo (lit : Lit) {lt : lit.var.idx < map.size} :
      state.denote (lit.mapTo map[lit.var.idx]) 0 assign swf = aig.denote lit 0 assign wf := by
    simp only [Lit.mapTo_eq, denote_eq, lt, ←denote]
    grind

include denote in
@[local grind =]
theorem denote_step {var var' inputsValid valid size}
    {idxInvalid : ∀ {idx}, aig[var'] = .input idx → ¬idx.validIn state} :
    let res := resetAig.step aig state map var' valid wf inputsValid size
    (lt : var.idx < res.snd.size) →
      res.fst.denote res.snd[var.idx] 0 assign = aig.denoteVar var 0 assign := by
  intro res h
  rw [show res.snd[var.idx] = (map.push res.snd[map.size])[var.idx] by simp [res, resetAig.step], Array.getElem_push]
  split
  · simp only [res, resetAig.step]
    grind
  · have : var = var' := by grind
    cases h : aig[var']
    <;> simp only [res, resetAig.step, Array.getElem_push_eq]
    <;> grind -splitMatch -splitIte

include denote in
theorem denote_go (lit : Lit.In aig) {it inputsValid valid size wf'} :
    let res := resetAig.go aig wf it state map swf inputsValid valid size
    res.fst.denote (res.snd lit) 0 assign wf' = aig.denote lit 0 assign := by
  fun_induction resetAig.go
  · grind only [denote_mapTo]
  next ih =>
    apply ih
    intros
    apply denote_step <;> grind

end denote_resetAig

@[simp, grind =]
theorem denote_resetAig {assign} {lit : Lit.In aig} :
    aig.resetAig.fst.denote (aig.resetAig.snd lit) 0 assign =
    aig.denote lit 0 assign wf := by
  grind [resetAig, denote_go]
