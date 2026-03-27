module

import all Valaig.Aig.Basic
public import Valaig.Aig.Semantics
public import Valaig.Aig.Iter

namespace Valaig.Aig
variable {aig : Aig} {wf : aig.WellFormed}

namespace resetAig

@[always_inline]
private def initLeaves (aig : Aig) : Aig :=
  aig.inputs.fold addInput' .empty

@[simp, grind .]
theorem Comb_initLeaves :
    (initLeaves aig).Comb := by
  simp only [initLeaves, ←Std.Iter.foldl_toList]
  apply List.foldlRecOn <;> grind

@[simp, grind .]
theorem WellFormed_initLeaves :
    (initLeaves aig).WellFormed := by
  suffices h : ∀ (list : List InputIdx) (state : Aig),
      state.WellFormed → list.Nodup → (∀ idx ∈ list, ¬idx.validIn state) →
      (list.foldl addInput' state).WellFormed by
    simp only [initLeaves, ←Std.Iter.foldl_toList]
    grind
  intro list state
  induction h : list generalizing list state <;> grind

@[simp, grind =]
theorem numInputs_initLeaves :
    (initLeaves aig).numInputs = aig.numInputs := by
  suffices h : ∀ (list : List InputIdx) (state : Aig),
      list.Nodup → (∀ idx ∈ list, ¬idx.validIn state) →
      (list.foldl addInput' state).numInputs = state.numInputs + list.length by
    simp only [initLeaves, ←Std.Iter.foldl_toList]
    grind [Std.Iter.length_toList_eq_length]
  intro list state
  induction h : list generalizing list state <;> grind

@[simp, grind .]
theorem input_validIn_initLeaves {idx : InputIdx} (valid : idx.validIn aig) :
    idx.validIn (initLeaves aig) := by
  suffices h : ∀ (tail : List InputIdx) (state : Aig),
      (∀ idx ∉ tail, idx.validIn aig → idx.validIn state) →
      idx.validIn (tail.foldl addInput' state) by
    simp only [initLeaves, ←Std.Iter.foldl_toList]
    grind
  intro list state
  induction h : list generalizing list state <;> grind

@[always_inline]
def step (aig : Aig) (state : Aig) (map : Array Lit) (var : Var)
    (valid : var.validIn aig := by grind)
    (wf : aig.WellFormed := by grind)
    (inputsValid : {idx : InputIdx} → idx.validIn aig → idx.validIn state := by grind)
    (valid : ∀ {lit},  lit ∈ map → lit.validIn state := by grind)
    (size : var.idx = map.size := by grind) :
    Aig × Array Lit :=
  let mapLit (lit : Lit) (h : lit.var < var := by grind) : Lit.In state :=
    lit.mapTo map[lit.var.idx] |>.castIn state

  let (eq:=_) (state, lit) : Aig × Lit :=
    match _ : aig[var] with
    | .false         => (state, .false)
    | .input idx     => (state, idx.getLit state)
    | .latch idx     => (state, mapLit (idx.getReset aig))
    | .and rhs0 rhs1 => state.addAnd (mapLit rhs0) (mapLit rhs1)

  (state, map.push lit)

variable {state : Aig} {map : Array Lit} {var : Var}
variable {valid : var.validIn aig}
variable {wf : aig.WellFormed}
variable {swf : state.WellFormed}
variable {inputsValid : {idx : InputIdx} → idx.validIn aig → idx.validIn state}
variable {valid : ∀ {lit},  lit ∈ map → lit.validIn state}
variable {size : var.idx = map.size}

@[simp, grind =]
theorem size_step :
    (step aig state map var).snd.size = map.size + 1 := by
  unfold step
  grind

@[simp, grind .]
theorem inputsValid_step {idx : InputIdx} (h : idx.validIn aig) :
    idx.validIn (step aig state map var).fst := by
  unfold step
  grind

include swf in
@[simp, grind .]
theorem WellFormed_step :
    (step aig state map var).fst.WellFormed := by
  unfold step
  grind

include swf in
@[simp, grind .]
theorem valid_step {lit} (h : lit ∈ (step aig state map var).snd) :
    lit.validIn (step aig state map var).fst := by
  simp_all [step]
  grind

end resetAig

/--
Construct a new Aig representing the values of nodes in the first cycle, assigning each
latch its reset value. This results in a combinational Aig with the same number of inputs
and a map to map from literals in the old Aig to the new one.
-/
def resetAig (aig : Aig) (wf : aig.WellFormed := by grind) : Aig × (Lit.In aig -> Lit) :=
  go aig.iter (resetAig.initLeaves aig) (.emptyWithCapacity aig.size)
where
  go it state (map : Array Lit)
      (wf : state.WellFormed := by grind)
      (inputsValid : {idx : InputIdx} → idx.validIn aig → idx.validIn state := by grind)
      (valid : ∀ {lit},  lit ∈ map → lit.validIn state := by grind)
      (size : (aig.iterVal it).idx = map.size := by grind) :=
    match it.step with
    | .done _ =>
      ⟨state, fun lit => lit.val.mapTo <| map[lit.val.var.idx]'(by grind [Var.validIn_iff])⟩
    | .yield it' var _ =>
      let (eq:=_) res := resetAig.step aig state map var
      go it' res.fst res.snd
  termination_by it.finitelyManySteps

namespace resetAig
variable {it : Std.Iter Var} {state : Aig} {map : Array Lit}
variable {swf : state.WellFormed}
variable {size : (aig.iterVal it).idx = map.size}

def go.induction
    (motive : (Aig × (Lit.In aig -> Lit)) -> Prop)
    (init : motive (state, (go aig wf it state map).snd))
    (ind :
      (it : Std.Iter Var) -> (state : Aig) -> (map : Array Lit) ->
      (swf : state.WellFormed) ->
      (inputsValid : {idx : InputIdx} → idx.validIn aig → idx.validIn state) ->
      (valid : ∀ {lit},  lit ∈ map → lit.validIn state) ->
      (valid' : (aig.iterVal it).validIn aig) ->
      (size : (aig.iterVal it).idx = map.size) ->
      (h : motive (state, (go aig wf it state map).snd)) ->
      motive ((step aig state map <| aig.iterVal it).fst, (go aig wf it state map).snd)) :
    let res := go aig wf it state map swf inputsValid valid size
    motive res := by
  fun_induction go
  · grind only
  next ih =>
    apply ih
    clear ih
    grind [go]

def induction
    (motive : (Aig × (Lit.In aig -> Lit)) -> Prop)
    (init : motive (initLeaves aig, (go aig wf aig.iter (initLeaves aig) (.emptyWithCapacity aig.size)).snd))
    (ind :
      (it : Std.Iter Var) -> (state : Aig) -> (map : Array Lit) ->
      (swf : state.WellFormed) ->
      (inputsValid : {idx : InputIdx} → idx.validIn aig → idx.validIn state) ->
      (valid : ∀ {lit},  lit ∈ map → lit.validIn state) ->
      (valid' : (aig.iterVal it).validIn aig) ->
      (size : (aig.iterVal it).idx = map.size) ->
      (h : motive (state, (go aig wf it state map).snd)) ->
      motive ((step aig state map <| aig.iterVal it).fst, (go aig wf it state map).snd)) :
    motive aig.resetAig := by
  apply go.induction motive <;> grind

end resetAig

@[simp, grind .]
theorem Comb_resetAig :
    aig.resetAig.fst.Comb := by
  apply resetAig.induction (·.fst.Comb)
  <;> (try unfold resetAig.step) <;> grind

@[simp, grind .]
theorem WellFormed_resetAig :
    aig.resetAig.fst.WellFormed := by
  apply resetAig.induction (·.fst.WellFormed)
  <;> (try unfold resetAig.step) <;> grind

@[simp, grind =]
theorem numInputs_resetAig :
    aig.resetAig.fst.numInputs = aig.numInputs := by
  apply resetAig.induction (·.fst.numInputs = aig.numInputs)
  <;> (try unfold resetAig.step) <;> grind

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
theorem denote_step {var var' inputsValid valid valid' size} :
    let res := resetAig.step aig state map var' valid wf inputsValid valid' size
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
  · grind only [denote_step]

end denote_resetAig

@[simp, grind =]
theorem denote_resetAig {assign} {lit : Lit.In aig} :
    aig.resetAig.fst.denote (aig.resetAig.snd lit) 0 assign =
    aig.denote lit 0 assign wf := by
  grind [resetAig, denote_go]
