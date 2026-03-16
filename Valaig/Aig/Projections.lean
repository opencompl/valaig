module

import all Valaig.Aig.Basic
public import Valaig.Aig.Semantics
public import Valaig.Aig.Iter

namespace Valaig.Aig
variable {aig : Aig} {wf : aig.WellFormed}

namespace projectComb

/--
Construct a new Aig with the right amount of inputs added that will be required by `projectComb`.
-/
@[always_inline]
def initLeaves (aig : Aig) (reset : Bool) : Aig :=
  size.repeat (·.addInput.fst) .empty
where
  size := if reset then aig.numInputs else aig.numInputs + aig.numLatches

variable {reset : Bool}

attribute [local simp, local grind] initLeaves.size

@[local simp, local grind .]
theorem Comb_initLeaves :
    (initLeaves aig reset).Comb := by
  unfold initLeaves
  induction initLeaves.size aig reset <;> grind [Nat.repeat]

@[local simp, local grind .]
theorem WellFormed_initLeaves :
    (initLeaves aig reset).WellFormed := by
  unfold initLeaves
  induction initLeaves.size aig reset <;> grind [Nat.repeat]

@[local simp, local grind =]
theorem numInputs_initLeaves :
  (initLeaves aig reset).numInputs = initLeaves.size aig reset := by
  unfold initLeaves
  induction initLeaves.size aig reset <;> grind [Nat.repeat]

/--
Maps an index from the original Aig to the one constructed by `initLeaves`.
-/
@[always_inline]
def mapIdx (aig : Aig) (idx : LeafIdx) : InputIdx :=
  match idx with
  | .input idx => idx
  | .latch idx => .ofIdx (idx.idx + aig.numInputs)

theorem mapIdx_validIn_initLeaves_input {idx : InputIdx} (valid : idx.validIn aig) :
    (mapIdx aig idx).validIn <| initLeaves aig reset := by
  grind [InputIdx.validIn_eq, mapIdx]

theorem mapIdx_validIn_initLeaves_latch {idx : LatchIdx} (valid : idx.validIn aig) :
    (mapIdx aig idx).validIn <| initLeaves aig false := by
  grind [InputIdx.validIn_eq, LatchIdx.validIn_eq, mapIdx]

end projectComb

attribute [local grind .] projectComb.WellFormed_initLeaves
attribute [local grind .] projectComb.mapIdx_validIn_initLeaves_input
attribute [local grind .] projectComb.mapIdx_validIn_initLeaves_latch

/--
Project out the reset and transition relation components of an Aig as new combinational Aigs.
These may go in the future, replaced by better methods for going straight to SAT
-/
def projectComb (aig : Aig) (reset : Bool) (wf : aig.WellFormed) : Aig × (Lit.In aig -> Lit) :=
  go aig.iter (projectComb.initLeaves aig reset) (.emptyWithCapacity aig.size)
where
  go it state (map : Array Lit)
      (wf : state.WellFormed := by grind)
      (inputMapsValid : {idx : InputIdx} → idx.validIn aig → (projectComb.mapIdx aig idx).validIn state := by grind)
      (latchMapsValid : reset = false → {idx : LatchIdx} → idx.validIn aig → (projectComb.mapIdx aig idx).validIn state := by grind)
      (valid : ∀ {lit} (_ : lit ∈ map), lit.validIn state := by grind)
      (size : it.val.idx = map.size := by grind) :=
    match it.step with
    | .done _ =>
      ⟨state, fun lit => lit.val.mapTo <| map[lit.val.var.idx]'(by grind [Var.validIn_eq])⟩
    | .yield it' var _ =>
      let mapLit (lit : Lit) (h : lit.var < var := by grind) : Lit.In state :=
        lit.mapTo map[lit.var.idx] |>.castIn state

      let res : Aig × Lit := 
        match _ : reset, _ : aig[var] with
        | _, .false =>         (state, .false)
        | _, .input idx
        | false, .latch idx => (state, (projectComb.mapIdx aig idx).getLit state)
        | true, .latch idx =>  (state, mapLit <| idx.getReset aig)
        | _, .and rhs0 rhs1 =>  state.addAnd (mapLit rhs0) (mapLit rhs1)

      go it' res.fst (map.push res.snd)
        (by subst res; grind only [usr WellFormed_addInput, usr WellFormed_addAnd])
        (by subst res; grind only [= input_validIn_addInput_iff, = input_validIn_addAnd_iff])
        (by subst res; grind only [= input_validIn_addInput_iff, = input_validIn_addAnd_iff])
        (by subst res; grind)
        (by subst res; grind only [Iter.val_yield, = Array.size_push])
  termination_by it.finitelyManySteps

section projectComb
variable {reset : Bool} {wf : aig.WellFormed} {it : Std.Iter Var} {state : Aig} {map : Array Lit}
variable {swf : state.WellFormed}
variable {size : it.val.idx = map.size}

@[local simp, local grind .]
theorem projectComb.Comb_go (comb : state.Comb) :
    (go aig reset wf it state map swf inputMapsValid latchMapsValid valid size).fst.Comb := by
  fun_induction go
  next => assumption
  next res ih => apply ih; subst res; grind

@[local simp, local grind .]
theorem projectComb.WellFormed_go :
    (go aig reset wf it state map swf inputMapsValid latchMapsValid valid size).fst.WellFormed := by
  fun_induction go <;> assumption

private theorem Comb_projectComb {reset} :
    (aig.projectComb reset wf).fst.Comb :=
  projectComb.Comb_go projectComb.Comb_initLeaves

private theorem WellFormed_projectComb {reset} :
    (aig.projectComb reset wf).fst.WellFormed :=
  projectComb.WellFormed_go

end projectComb

@[inline]
def resetAig (aig : Aig) (wf : aig.WellFormed := by grind) : Aig × (Lit.In aig -> Lit) :=
  projectComb aig true wf

@[simp, grind .]
theorem Comb_resetAig :
    (aig.resetAig wf).fst.Comb :=
  Comb_projectComb

@[simp, grind .]
theorem WellFormed_resetAig :
    (aig.resetAig wf).fst.WellFormed :=
  WellFormed_projectComb

@[inline]
def transAig (aig : Aig) (wf : aig.WellFormed := by grind) : Aig × (Lit.In aig -> Lit) :=
  projectComb aig false wf

@[simp, grind .]
theorem Comb_transAig :
    (aig.transAig wf).fst.Comb :=
  Comb_projectComb

@[simp, grind .]
theorem WellFormed_transAig :
    (aig.transAig wf).fst.WellFormed :=
  WellFormed_projectComb

/--
Map a leaf index from the original aig into the corresponding input to the result of `transAig`.
-/
def transAig.mapIdx (aig : Aig) (idx : LeafIdx) : InputIdx :=
  projectComb.mapIdx aig idx
