module

import all Valaig.Aig.Basic
public import Valaig.Aig.Semantics
public import Valaig.Aig.Iter

/-
Project out the reset and transition relation components of an Aig as new combinational Aigs.
These may go in the future, replaced by better methods for going straight to SAT
-/

public section
namespace Valaig.Aig
variable {aig : Aig} {wf : aig.WellFormed}

private def projectComb (aig : Aig) (reset : Bool) (wf : aig.WellFormed) : Aig × (Lit.In aig -> Lit) :=
  go aig.iter .empty (.emptyWithCapacity aig.size)
where
  go iter (state : Aig) (map : Array Lit)
    (size : iter.var.idx = map.size := by grind)
    (valid : ∀ {lit} (_ : lit ∈ map), lit.validIn state := by grind) :=
    match h : iter.step.val with
    | .skip it => go iter state map
    | .done =>
      ⟨state, fun lit => lit.val.mapTo <| map[lit.val.var.idx]'(by grind [Var.validIn_eq_lt_size])⟩
    | .yield it' var =>
      let mapLit (lit : Lit) (h : lit.var < var := by grind) : Lit :=
        lit.mapTo map[lit.var.idx]

      let res : Aig × Lit := 
        match _ : reset, _ : aig[var] with
        | _, .false => (state, .false)
        | _, .input _ | false, .latch _ =>
          let (eq:=_) (state, idx) := state.addInput
          (state, idx.getLit state)
        | true, .latch idx => (state, mapLit <| idx.getReset aig)
        | _, .and rhs0 rhs1 => state.addAnd (mapLit rhs0) (mapLit rhs1)

      go it' res.fst (map.push res.snd) (by simp; grind) (by simp [res]; grind)
  termination_by iter.length
  decreasing_by all_goals grind

section projectComb
variable {reset : Bool} {state : Aig} {map : Array Lit} {iter : Std.Iter Var}
variable {size : iter.var.idx = map.size}

@[local simp, local grind .]
private theorem projectComb.Comb_go (comb : state.Comb) :
    (go aig reset wf iter state map size valid).fst.Comb := by
  fun_induction go
  · grind only
  · grind only
  next res ih =>
    apply ih
    subst res
    grind

@[local simp, local grind .]
private theorem projectComb.WellFormed_go (swf : state.WellFormed) :
    (go aig reset wf iter state map size valid).fst.WellFormed := by
  fun_induction go
  · grind only
  · grind only
  next res ih =>
    apply ih
    subst res
    grind

private theorem Comb_projectComb {reset} :
    (aig.projectComb reset wf).fst.Comb :=
  projectComb.Comb_go (by simp)

private theorem WellFormed_projectComb {reset} :
    (aig.projectComb reset wf).fst.WellFormed :=
  projectComb.WellFormed_go (by simp)

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
