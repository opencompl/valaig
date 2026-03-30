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

namespace resetAig

variable {state : Aig} {map : Array Lit} {swf : state.WellFormed}
variable {denote : ∀ {assign} {var : Var} (lt : var.idx < map.size),
           state.denoteComb map[var.idx] assign = aig.denoteResetVar var assign}
variable {assign : LeafIdx -> Bool}

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

end resetAig

@[simp, grind =]
theorem denote_resetAig {assign} {lit : Lit.In aig} :
    aig.resetAig.fst.denoteComb (aig.resetAig.snd lit) assign =
    aig.denoteReset lit assign wf := by
  grind [resetAig, resetAig.denote_go]

namespace transAig

@[always_inline]
def step (aig : Aig) (state : Aig) (map : Array Lit) (var : Var)
    (valid : var.validIn aig := by grind)
    (wf : aig.WellFormed := by grind)
    (mono : aig ≤ state := by grind)
    (valid : ∀ lit ∈ map, lit.validIn state := by grind)
    (size : var.idx = map.size := by grind) :
    Aig × Array Lit :=
  let mapLit (lit : Lit) (h : lit.var < var := by grind) : Lit.In state :=
    lit.mapTo map[lit.var.idx] |>.castIn state

  let (eq:=_) (state, lit) : Aig × Lit :=
    match _ : aig[var] with
    | .false         => (state, .false)
    | .input _       => let (eq:=_) (state, idx) := state.addInput
                        (state, idx.getLit state)
    | .latch idx     => (state, idx.getNext state)
    | .and rhs0 rhs1 => state.addAnd (mapLit rhs0) (mapLit rhs1)

  (state, map.push lit)

variable {aig state : Aig} {map : Array Lit} {var : Var}
variable {valid : var.validIn aig} {wf : aig.WellFormed}
variable {mono : aig ≤ state} {valid : ∀ lit ∈ map, lit.validIn state}
variable {size : var.idx = map.size}

@[simp, grind =]
theorem size_step :
    (step aig state map var).snd.size = map.size + 1 := by
  unfold step
  grind

@[simp, grind =]
theorem step_snd_eq :
    (step aig state map var).snd = map.push ((step aig state map var).snd[map.size]) := by
  unfold step
  grind

@[simp, grind .]
theorem mono_step :
    state ≤ (step aig state map var).fst := by
  unfold step
  grind

grind_pattern mono_step => (step aig state map var).fst

@[simp, grind .]
theorem WellFormed_step {swf : state.WellFormed} :
    (step aig state map var).fst.WellFormed := by
  unfold step
  grind

@[simp, grind .]
theorem valid_step {swf : state.WellFormed} :
    let res := step aig state map var
    ∀ lit ∈ res.snd, lit.validIn res.fst := by
  unfold step
  grind

end transAig

def transAig (aig : Aig) (wf : aig.WellFormed := by grind) :  Aig × (Lit.In aig -> Fin 2 -> Lit) :=
  go aig.iter aig (.emptyWithCapacity aig.size)
where
  go it (state : Aig) (map : Array Lit)
      (wf : state.WellFormed := by grind)
      (mono : aig ≤ state := by grind)
      (valid : ∀ lit ∈ map, lit.validIn state := by grind)
      (size : (aig.iterVal it).idx = map.size := by grind) :
      Aig × (Lit.In aig -> Fin 2 -> Lit) :=
    match it.step with
    | .done _ =>
      ⟨state, fun lit frame =>
        match frame with
        | 0 => lit
        | 1 => lit.val.mapTo <| map[lit.val.var.idx]'(by grind [Var.validIn_iff])⟩
    | .yield it' var _ =>
      let (eq:=_) res := transAig.step aig state map var
      go it' res.fst res.snd
  termination_by it.finitelyManySteps

@[simp, grind .]
theorem WellFormed_transAig :
    aig.transAig.fst.WellFormed := by
  unfold transAig
  apply WellFormed_go
where
  WellFormed_go {a b c d e f g} :
      (transAig.go aig wf a b c d e f g).fst.WellFormed := by
    fun_induction transAig.go <;> grind

@[simp]
theorem transAig.mono_go {a state c d e f g} :
    state ≤ (transAig.go aig wf a state c d e f g).fst := by
  fun_induction transAig.go <;> grind

grind_pattern transAig.mono_go => (transAig.go aig wf a state c).fst

@[simp]
theorem mono_transAig :
    aig ≤ aig.transAig.fst := by
  unfold transAig
  apply transAig.mono_go

grind_pattern mono_transAig => aig.transAig.fst

@[simp, grind =]
theorem transAig_map_zero {lit : Lit.In aig} :
    aig.transAig.snd lit 0 = lit := by
  unfold transAig
  apply go_map_zero
where
  go_map_zero {a b c d e f g} :
      let res := transAig.go aig wf a b c d e f g
      res.snd lit 0 = lit := by
    fun_induction transAig.go <;> grind

@[simp, grind .]
theorem transAig.go_validIn {lit : Lit.In aig} {frame : Fin 2} {a b c d e f g} :
    let res := transAig.go aig wf a b c d e f g
    (res.snd lit frame).validIn res.fst := by
  fun_induction transAig.go <;> grind

@[simp, grind .]
theorem transAig_validIn {lit : Lit.In aig} {frame : Fin 2} :
    (aig.transAig.snd lit frame).validIn aig.transAig.fst := by
  unfold transAig
  apply transAig.go_validIn

@[simp, grind =]
theorem transAig_map_matches_input {idx : InputIdx} (valid : idx.validIn aig) :
      aig.transAig.fst[(aig.transAig.snd (idx.getLit aig |>.castIn aig) 1).var] matches .input _ := by
  unfold transAig
  apply go <;> grind
where
  go {it state map a b c d} {lit : Lit.In aig} {swf : state.WellFormed}
      {ih : ∀ {lit : Lit.In aig} (lt : lit.val.var.idx < map.size),
        aig[lit.val.var] matches .input _ →
          state[map[lit.val.var.idx].var] matches .input _} :
      let res := transAig.go aig wf it state map a b c d
      aig[lit.val.var] matches .input _ →
        res.fst[res.snd lit 1 |>.var] matches .input _ := by
    fun_induction transAig.go
    · simp only
      unfold transAig.go
      grind
    next eq res _ ih1 =>
      simp only
      unfold transAig.go
      simp only [eq]
      simp only at ih1
      apply ih1
      · grind
      · clear ih1
        grind [transAig.step]

/--
TODO: This should be discouraged against actually using as it can break linearity
-/
@[always_inline]
def transAig.mapIdx (idx : LeafIdx) (frame : Frame) : LeafIdx :=
  match frame, _ : idx, _ : decide (idx.validIn aig) with
  | 1, .input idx, true =>
    match h : aig.transAig.fst[(aig.transAig.snd (idx.getLit aig |>.castIn aig) 1).var] with
    | .input idx => idx
    | .false
    | .latch _
    | .and _ _ => by grind [transAig_map_matches_input]
  | _, _, _ => idx
