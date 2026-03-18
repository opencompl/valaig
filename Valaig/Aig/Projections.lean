module

import all Valaig.Aig.Basic
public import Valaig.Aig.Semantics
public import Valaig.Aig.Iter

namespace Valaig.Aig
variable {aig : Aig} {wf : aig.WellFormed}

namespace resetAig

@[always_inline]
private def initLeaves (aig : Aig) : Aig :=
  aig.numInputs.repeat (·.addInput.fst) .empty

@[simp, grind .]
theorem Comb_initLeaves :
    (initLeaves aig).Comb := by
  unfold initLeaves
  induction aig.numInputs <;> grind [Nat.repeat]

@[simp, grind .]
theorem WellFormed_initLeaves :
    (initLeaves aig).WellFormed := by
  unfold initLeaves
  induction aig.numInputs <;> grind [Nat.repeat]

@[simp, grind =]
theorem numInputs_initLeaves :
  (initLeaves aig).numInputs = aig.numInputs := by
  unfold initLeaves
  induction aig.numInputs <;> grind [Nat.repeat]

@[simp, grind .]
theorem input_validIn_initLeaves {idx : InputIdx} (valid : idx.validIn aig) :
  idx.validIn (initLeaves aig) := by
  grind [InputIdx.validIn_eq]

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
      (size : it.val.idx = map.size := by grind) :=
    match it.step with
    | .done _ =>
      ⟨state, fun lit => lit.val.mapTo <| map[lit.val.var.idx]'(by grind [Var.validIn_eq])⟩
    | .yield it' var _ =>
      let mapLit (lit : Lit) (h : lit.var < var := by grind) : Lit.In state :=
        lit.mapTo map[lit.var.idx] |>.castIn state

      match _ : aig[var] with
      | .false     => go it' state <| map.push .false
      | .input idx => go it' state <| map.push <| idx.getLit state
      | .latch idx => go it' state <| map.push <| mapLit (idx.getReset aig)
      | .and rhs0 rhs1 =>
        let (eq:=_) (state, lit) := state.addAnd (mapLit rhs0) (mapLit rhs1)
        go it' state <| map.push lit
  termination_by it.finitelyManySteps

-- Mark it as Comb, WellFormed, inputs valid iff, matching semantics

namespace resetAig
variable {it : Std.Iter Var} {state : Aig} {map : Array Lit}
variable {swf : state.WellFormed}
variable {size : it.val.idx = map.size}

@[simp, grind .]
theorem Comb_go (comb : state.Comb) :
    (go aig wf it state map swf inputsValid valid size).fst.Comb := by
  fun_induction go <;> grind

@[simp, grind .]
theorem WellFormed_go :
    (go aig wf it state map swf inputsValid valid size).fst.WellFormed := by
  fun_induction go <;> assumption

@[simp, grind =]
theorem numInputs_go :
    (go aig wf it state map swf inputsValid valid size).fst.numInputs = state.numInputs := by
  fun_induction go <;> grind

@[simp, grind .]
theorem go_validIn {lit : Lit.In aig} :
    let res := go aig wf it state map swf inputsValid valid size
    (res.snd lit).validIn res.fst := by
  fun_induction go <;> grind

@[simp, grind .]
theorem input_validIn_go {idx : InputIdx} (valid : idx.validIn aig) :
    idx.validIn (go aig wf it state map swf inputsValid valid' size).fst := by
  fun_induction go <;> grind

@[simp, grind =]
theorem go_map_eq {lit : Lit.In aig} (lt : lit.val.var < it.val) :
    (go aig wf it state map swf inputsValid valid' size).snd lit =
    (lit.val.mapTo map[lit.val.var.idx]) := by
  fun_induction go <;> grind

@[simp, grind .]
theorem Monotone_go :
    state ≤ (go aig wf it state map swf inputsValid valid' size).fst := by
  fun_induction go <;> grind

-- TODO: This needs tidying badly
@[simp, grind .]
theorem denote_go {assign} {lit : Lit} (valid : lit.validIn aig)
    (h : ∀ {var' : Var} (_ : var'.validIn aig) (_ : var' < it.val),
      state.denote map[var'.idx] 0 assign = aig.denoteVar var' 0 assign) :
    let res := go aig wf it state map swf inputsValid valid' size
    res.fst.denote (res.snd ⟨lit, valid⟩) 0 assign =
    aig.denote lit 0 assign := by
  intro res
  generalize heq : go aig wf it state map swf inputsValid valid' size = aaa
  have : res = aaa := by grind
  simp only [this]
  fun_induction go
  · grind [go]
  · unfold go at heq
    split at heq
    · grind
    · split at heq
      · grind [Var.ext_idx]
      · grind
      · grind
      · grind
  · unfold go at heq
    grind [Var.ext_idx]
  · unfold go at heq
    split at heq
    · grind
    · split at heq
      · grind
      · grind
      · simp_all [-denote_eq]
        rename_i var _ _ idx _ _ ih _
        apply ih
        · clear ih
          intro var' _ _
          grind [Var.ext_idx]
        · grind
        · trivial
      · grind
  · unfold go at heq
    split at heq
    · grind
    · split at heq
      · grind
      · grind
      · grind
      · simp_all [-denote_eq]
        rename_i var _ _ _ _ heq _ ih _
        apply ih
        · clear ih
          intro var' _ _
          simp only [Array.getElem_push]
          split
          · grind
          · clear heq
            have : var = var' := by grind [Var.ext_idx]
            grind
        · grind
        · trivial

end resetAig

@[simp, grind .]
theorem Comb_resetAig :
    aig.resetAig.fst.Comb := by
  grind [resetAig]

@[simp, grind .]
theorem WellFormed_resetAig :
    aig.resetAig.fst.WellFormed := by
  grind [resetAig]

@[simp, grind =]
theorem numInputs_resetAig :
    aig.resetAig.fst.numInputs = aig.numInputs := by
  grind [resetAig]

@[simp, grind .]
theorem resetAig_validIn {lit : Lit.In aig} :
    (aig.resetAig.snd lit).validIn aig.resetAig.fst := by
  grind [resetAig]

@[simp, grind .]
theorem denote_resetAig {assign} {lit : Lit} (valid : lit.validIn aig) :
    aig.resetAig.fst.denote (aig.resetAig.snd ⟨lit, valid⟩) 0 assign =
    aig.denote lit 0 assign := by
  grind [resetAig]
