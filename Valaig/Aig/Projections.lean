module

import all Valaig.Aig.Basic
public import Valaig.Aig.Semantics
public import Valaig.Aig.Iter

namespace Valaig.Aig
/-
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
           ⟦state, map[var.idx], assign⟧c0 = ⟦aig, var, assign⟧sv0}
variable {assign : LeafIdx -> Frame -> Bool}
include denote

theorem denote_mapTo (lit : Lit) {lt : lit.var.idx < map.size} :
      ⟦state, lit.mapTo map[lit.var.idx], assign⟧c0 = ⟦aig, lit, assign⟧s0 := by
    grind

@[local grind =]
theorem denote_step {var var' a b c}
    {inputInvalid : ∀ {idx}, aig[var'] = .input idx → ¬idx.validIn state}
    {latchInvalid : ∀ {idx}, aig[var'] = .latch idx → ¬idx.validIn state} :
    let res := resetAig.step aig state map var' a wf b c
    (lt : var.idx < res.snd.size) →
      ⟦res.fst, res.snd[var.idx], assign⟧c0 = ⟦aig, var, assign⟧sv0 := by
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

theorem denote_go (lit : Lit.In aig) {it a b c d wf'} :
    let res := resetAig.go aig wf it state map swf a b c d
    res.fst.denoteC (res.snd lit) assign 0 wf' = ⟦aig, lit, assign⟧s0 := by
  fun_induction resetAig.go
  · grind only [denote_mapTo]
  next ih =>
    apply ih
    intros
    apply denote_step <;> grind

end resetAig

@[simp, grind =]
theorem denote_resetAig {assign} {lit : Lit.In aig} :
    ⟦aig.resetAig.fst, aig.resetAig.snd lit, assign⟧c0 = ⟦aig, lit, assign⟧s0 := by
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
  go {it state map a b c d} {lit : Lit.In aig}
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
    · simp only
      unfold transAig.go
      grind -splitIte [transAig.step]

/--
NOTE: This should not be used for computation as it can break linearity
-/
@[always_inline]
def transAig.mapIdx (aig : Aig) (idx : LeafIdx) (frame : Frame) (wf : aig.WellFormed := by grind) : LeafIdx :=
  match frame, _ : idx, _ : decide (idx.validIn aig) with
  | 1, .input idx, true =>
    match h : aig.transAig.fst[(aig.transAig.snd (idx.getLit aig |>.castIn aig) 1).var] with
    | .input idx => idx
    | .false
    | .latch _
    | .and _ _ => by grind [transAig_map_matches_input]
  | _, _, _ => idx

@[always_inline]
def transAig.mapAssign (aig : Aig) (assign : LeafIdx -> Frame -> Bool) (wf : aig.WellFormed := by grind) :
    LeafIdx -> Frame -> Bool :=
  fun idx frame =>
    assign (transAig.mapIdx aig idx frame wf) frame

-- @[simp, grind =]
theorem denote_transAig_one {assign} {lit : Lit.In aig} :
    ⟦aig.transAig.fst, aig.transAig.snd lit 1, transAig.mapAssign aig assign⟧c0 = ⟦aig, lit, assign⟧c1 := by
  sorry

-/

namespace copyComb

inductive Leaf (src dest : Aig) (idx : LeafIdx.In src) where
| srcLit : (lit : Lit) -> lit.var < idx.val.getVar src -> Leaf src dest idx
| destLit : Lit.In dest -> Leaf src dest idx

abbrev LeafMap (src dest : Aig) := (idx : LeafIdx.In src) -> Leaf src dest idx

variable {src dest : Aig} {map : LeafMap src dest}

@[local grind, ext]
structure State (map : LeafMap src dest) where
  aig : Aig
  map : Array Lit

  srcWf : src.WellFormed := by grind
  destWf : dest.WellFormed := by grind
  wf : aig.WellFormed := by grind
  mono : dest ≤ aig := by grind
  valid : ∀ lit ∈ map, lit.validIn aig := by grind
  size : map.size ≤ src.size := by grind

namespace State
variable {s : State map}

@[always_inline, simp, grind]
def var (s : State map) : Var :=
  .ofIdx s.map.size

@[always_inline]
def mapVar (s : State map) (var : Var) (h : var < s.var := by grind) : Lit :=
  s.map[var.idx]

@[simp, grind .]
theorem validIn_mapVar {var : Var} (h : var < s.var := by grind) :
    (s.mapVar var h).validIn s.aig := by
  grind [mapVar]

@[always_inline]
def mapLit (s : State map) (lit : Lit) (h : lit.var < s.var := by grind) : Lit :=
  lit.mapTo (s.mapVar lit.var) |>.castIn s.aig (by grind [mapVar])

@[simp, grind .]
theorem validIn_mapLit {lit : Lit} (h : lit.var < s.var) :
    (s.mapLit lit h).validIn s.aig := by
  grind [mapVar, mapLit]

def denoteLeaf (s : State map) (assign : LeafIdx -> Frame -> Bool) : LeafIdx -> Frame -> Bool :=
  fun idx frame =>
    match _ : decide (idx.validIn src) with
    | false           => false
    | true            =>
      have valid := by grind
      match map <| idx.castIn src valid with
      | .destLit lit  => ⟦dest, lit, frame, assign⟧c
      | .srcLit lit h =>
        match _ : decide (lit.var < s.var) with
        | false       => false
        | true        => ⟦s.aig, s.mapLit lit, frame, assign⟧c

@[always_inline]
def nextLit (s : State map) (h : s.var.validIn src := by grind) : Aig × Lit :=
  match _ : src[s.var] with
  | .false          => (s.aig, false)
  | .and rhs0 rhs1  => s.aig.addAnd (s.mapLit rhs0) (s.mapLit rhs1)
  | .input idx
  | .latch idx      =>
    have valid := by grind
    match map (idx.castIn src valid) with
    | .srcLit lit _ => (s.aig, s.mapLit lit)
    | .destLit lit  => (s.aig, lit)

section nextLit
variable {h : s.var.validIn src}

@[simp, grind .]
theorem validIn_nextLit :
    s.nextLit.snd.validIn s.nextLit.fst := by
  unfold nextLit
  split <;> (try simp only; split) <;> grind

@[simp]
theorem mono_nextLit :
    s.aig ≤ s.nextLit.fst := by
  unfold nextLit
  split <;> (try simp only; split) <;> grind

grind_pattern mono_nextLit => s.nextLit.fst

@[simp]
theorem mono_nextLit' :
    dest ≤ s.nextLit.fst := by
  grind [nextLit]

grind_pattern mono_nextLit' => s.nextLit.fst

@[simp, grind .]
theorem WellFormed_nextLit :
    s.nextLit.fst.WellFormed := by
  unfold nextLit
  split <;> (try simp only; split) <;> grind

end nextLit

@[always_inline]
def step (s : State map) (h : s.var.validIn src := by grind) : State map :=
  let (eq:=_) (aig, lit) := s.nextLit
  let map := s.map.push lit
  .mk aig map (valid := by
    simp only [Array.mem_push, map]
    rintro _ (_ | _) <;> grind
  )

section step
variable {h : s.var.validIn src}

@[simp, grind =]
theorem size_step :
    s.step.map.size = s.map.size + 1 := by
  grind [step]

end step

end State

@[local grind, ext]
structure Result (map : LeafMap src dest) extends State map where
  sized : map.size = src.size := by grind [Var.validIn_iff]

namespace Result

@[inline]
def mapVar (res : Result map) (var : Var) (valid : var.validIn src := by grind) : Lit :=
  State.mapVar res.toState var

@[inline]
def mapLit (res : Result map) (lit : Lit) (valid : lit.validIn src := by grind) : Lit :=
  State.mapLit res.toState lit

end Result

attribute [local simp, local grind] Result.mapVar Result.mapLit

@[always_inline]
def go (aig : Aig) (smap : Array Lit) (h : ∃ (s : State map), s.aig = aig ∧ s.map = smap := by grind) : Result map :=
  let s : State map := .mk aig smap
  match h : decide (s.var.validIn src) with
  | false => .mk s
  | true =>
    let s := s.step
    go s.aig s.map
termination_by src.size - smap.size
decreasing_by grind

def goSlow (s : State map) : Result map :=
  match h : decide (s.var.validIn src) with
  | false => .mk s
  | true => goSlow s.step
termination_by src.size - s.map.size
decreasing_by grind

section go
variable {s : State map}

@[simp, grind =]
theorem go_eq_goSlow {aig : Aig} {smap : Array Lit} {h : ∃ (s : State map), s.aig = aig ∧ s.map = smap} :
    go aig smap h = goSlow (.mk aig smap) := by
  fun_induction go <;> unfold goSlow <;> grind

@[simp]
theorem prefix_goSlow_map :
    s.map.toList <+: (goSlow s).map.toList := by
  fun_induction goSlow
  · simp
  next s h ih =>
    apply List.IsPrefix.trans ?_ ih
    grind [State.step]

@[simp]
theorem mono_goSlow :
    s.aig ≤ (goSlow s).aig := by
  fun_induction goSlow <;> grind [State.step]

grind_pattern mono_goSlow => (goSlow s).aig

@[simp, grind =]
theorem mapVar_goSlow_of_lt {var : Var} (lt : var < s.var) (valid : var.validIn src)  :
    (goSlow s).mapVar var valid = s.mapVar var := by
  fun_induction goSlow <;> grind [State.step, State.mapVar]

@[simp, grind =]
theorem mapLit_toState_goSlow_of_lt {lit : Lit} (lt : lit.var < s.var) h :
    (goSlow s).toState.mapLit lit h = s.mapLit lit := by
  fun_induction goSlow <;> grind [State.step, State.mapVar, State.mapLit]

@[simp, grind =]
theorem var_goSlow :
    (goSlow s).var = .ofIdx src.size := by
  fun_induction goSlow <;> grind [Var.validIn_iff]

theorem denoteC_mapVar_goSlow {assign} {var : Var} (valid : var.validIn src) {frame : Frame}
    (inv :
      ∀ {var : Var} (lt : var < s.var) {frame : Frame},
        ⟦s.aig, s.mapVar var, frame, assign⟧c =
        ⟦src, var, frame, s.denoteLeaf assign⟧cv) :
    have := goSlow s |>.wf
    ⟦goSlow s |>.aig, goSlow s |>.mapVar var, frame, assign⟧c =
    ⟦src, var, frame, goSlow s |>.denoteLeaf assign⟧cv := by
  fun_induction goSlow
  · unfold goSlow; grind
  next s h ih =>
    simp only
    by_cases lt : var < s.var
    · rw [mapVar_goSlow_of_lt]
      · rw [denoteC_mono (old := s.aig)]
        · have := inv lt (frame := frame)
          rw [this, denoteCV_of_assign_eq]
          · intro idx frame' valid le
            unfold State.denoteLeaf
            split
            · grind
            · simp only
              split
              · grind
              · split
                · split
                  · grind
                  · rcases le with a | b
                    · clear ih inv;
                      rename_i lit _ _ _ _
                      sorry
                    · grind
                · split
                  · grind
                  · grind
          · grind
        · grind
        · grind
        · grind
        · exact (goSlow s).wf
      · grind
    · by_cases var = s.var
      · sorry
      · sorry

end go

end copyComb

@[inline]
def copyComb (src dest : Aig) (map : copyComb.LeafMap src dest) (srcWf : src.WellFormed := by grind)
    (destWf : dest.WellFormed := by grind) : copyComb.Result map :=
  let s : copyComb.State map := .mk dest (.emptyWithCapacity dest.size)
  copyComb.go s.aig s.map (by exists s)

section copyComb
variable {src dest : Aig} {map : copyComb.LeafMap src dest} {srcWf : src.WellFormed} {destWf : dest.WellFormed}

@[simp]
theorem mono_copyComb :
    dest ≤ (src.copyComb dest map).aig :=
  (src.copyComb dest map).mono

grind_pattern mono_copyComb => (src.copyComb dest map).aig

@[simp, grind .]
theorem WellFormed_copyComb :
    (src.copyComb dest map).aig.WellFormed :=
  (src.copyComb dest map).wf

theorem denoteC_mapVar_copyComb {assign} {var : Var} (valid : var.validIn src) {frame : Frame} :
    ⟦(src.copyComb dest map).aig, (src.copyComb dest map).mapVar var, frame, assign⟧c =
    ⟦src, var, frame, (src.copyComb dest map).denoteLeaf assign⟧cv := by
  sorry

end copyComb
