module

import all Valaig.Aig.Basic
public import Valaig.Aig.WellFormed
public import Valaig.Aig.Iter

/-
Project out the reset and transition relation components of an Aig as new combinational Aigs.
These may go in the future, replaced by better methods for going straight to SAT
-/

public section
namespace Valaig.Aig

def resetAig (aig : Aig) (wf : aig.WellFormed) : Aig :=
  go aig.iter .empty (.emptyWithCapacity aig.size)
where
  go iter (state : Aig) (map : Array Lit)
    (size : iter.var.idx = map.size := by grind)
    (valid : ∀ {lit} (_ : lit ∈ map), lit.validIn state := by grind) :=
    match h : iter.step.val with
    | .skip it => go iter state map
    | .done => state
    | .yield it' var =>
      let mapLit (lit : Lit) (h : lit.var < var := by grind) : Lit :=
        map[lit.var.idx]'(by grind) |>.invert lit.inverted

      let res : Aig × Lit := 
        match h : aig[var]'(by grind) with
        | .false => (state, .false)
        | .input _ =>
          let (eq:=_) (state, idx) := state.addInput
          (state, idx.getLit state)
        | .latch idx => (state, mapLit <| idx.getReset aig)
        | .and rhs0 rhs1 => state.addAnd (mapLit rhs0) (mapLit rhs1)

      go it' res.fst (map.push res.snd) (by simp; grind) (by simp [res]; grind)
  termination_by iter.length
  decreasing_by all_goals grind

def transAig (aig : Aig) (wf : aig.WellFormed) : Aig :=
  go aig.iter .empty (.emptyWithCapacity aig.size)
where
  go iter (state : Aig) (map : Array Lit)
    (size : iter.var.idx = map.size := by grind)
    (valid : ∀ {lit} (_ : lit ∈ map), lit.validIn state := by grind) :=
    match h : iter.step.val with
    | .skip it => go iter state map
    | .done => state
    | .yield it' var =>
      let mapLit (lit : Lit) (h : lit.var < var := by grind) : Lit :=
        map[lit.var.idx]'(by grind) |>.invert lit.inverted

      let res : Aig × Lit := 
        match h : aig[var]'(by grind) with
        | .false => (state, .false)
        | .input _ | .latch _ =>
          let (eq:=_) (state, idx) := state.addInput
          (state, idx.getLit state)
        | .and rhs0 rhs1 => state.addAnd (mapLit rhs0) (mapLit rhs1)

      go it' res.fst (map.push res.snd) (by simp; grind) (by simp [res]; grind)
  termination_by iter.length
  decreasing_by all_goals grind
