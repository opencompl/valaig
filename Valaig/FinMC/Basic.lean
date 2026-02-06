module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finite.Card

public section
namespace Valaig.FinMC

/-
A theory of Model Checking for finite-state transition systems.
-/

/--
A transition system over some domain α has predicates
defining the initial states and the transition relation between states.
-/
structure TransSys (α : Type) where
  init : α -> Prop
  trans : α -> α -> Prop

/--
A finite path on a transition system is a finite sequence of states (stored as
an array) such that each pair are related by the transition relation.
-/
structure FinPath {α : Type} (ts : TransSys α) where
  states : Array α
  sized : states.size ≠ 0

  trans :
    ∀ {i : Nat} (_ : i < states.size - 1),
      ts.trans states[i] states[i + 1]

attribute [grind .] FinPath.sized

namespace FinPath
variable {α : Type} {ts : TransSys α}

abbrev size (path : FinPath ts) : Nat :=
  path.states.size

instance {path : FinPath ts} : NeZero (path.size) := by
  rw [neZero_iff]
  exact path.sized

abbrev state (path : FinPath ts) (idx : Nat) (bound : idx < path.size := by get_elem_tactic) : α :=
  path.states[idx]

/--
The initial state of a path is the state with the lowest index.
-/
def initial (path : FinPath ts) : α :=
  have := path.sized
  path.states[0]

/--
The final state of a path is the state with the greatest index.
-/
def final (path : FinPath ts) : α :=
  have := path.sized
  path.states.back

/--
The index of `final`.
-/
abbrev lastIdx (path : FinPath ts) : Nat :=
  path.size - 1

/--
A path between two states is a path such that the initial and final states
are these states.
-/
def Between (path : FinPath ts) (initial final : α) : Prop :=
  path.initial = initial ∧ path.final = final

/--
A path is simple if it does not visit the same state twice.
-/
@[expose, reducible, simp]
def Simple (path : FinPath ts) : Prop :=
  ∀ {i j : Nat} (_ : i < path.size) (_ : j < path.size),
    i ≠ j →
      path.state i ≠ path.state j

abbrev SimplePath {α : Type} (ts : TransSys α) :=
  { path : FinPath ts // path.Simple }

/--
Construct a trivial path from a single state.
-/
def trivial (state : α) : FinPath ts :=
  {
    states := #[state],
    sized := by simp
    trans := by simp
  }

/--
Add a new state to the end of the path that obeys the transition relation.
-/
def push (path : FinPath ts) (state : α) (trans : ts.trans path.final state := by grind) :
    FinPath ts :=
  {
    states := path.states.push state,
    sized := by simp,
    trans := by grind [FinPath.trans, final]
  }

namespace removeLoops
variable [DecidableEq α] {path : FinPath ts} {idx : Nat} {bound : idx < path.size}
variable {state : α}

/--
Returns the greatest index in `path` that is equal to `state` and at most `idx`,
if one exists.
-/
private def findIdx [DecidableEq α] (path : FinPath ts)
    (state : α) (idx : Nat) (bound : idx < path.size := by lia) : Option Nat :=
  if path.state idx = state then
    some idx
  else if h : idx = 0 then
    none
  else
    findIdx path state (idx - 1)

private theorem findIdx_lt :
    match findIdx path state idx bound with
    | some n => n ≤ idx
    | _ => True := by
  fun_induction findIdx
  · simp
  · simp
  · grind only [Option.all_eq_true]

private theorem findIdx_eq :
    match _ : findIdx path state idx bound with
    | some n =>
      path.state n (by grind only [findIdx_lt]) = state
    | _ => True := by
  fun_induction findIdx
  <;> grind only [findIdx]

private theorem findIdx_eq_none_implies_forall_ne :
    match _ : findIdx path state idx bound with
    | none =>
      ∀ {idx' : Nat} (_ : idx' ≤ idx), path.state idx' ≠ state
    | _ => True := by
  fun_induction findIdx
  · simp
  · grind only
  · grind only

private def removeUpTo
    [DecidableEq α] (path : FinPath ts) (idx : Nat)
    (bound : idx < path.size := by grind) :
    { path' : FinPath ts // path'.final = path.state idx } :=
  if hidx : idx = 0 then
    ⟨.trivial path.initial, by simp_all [final, FinPath.state, initial, trivial]⟩
  else
    let state := path.state idx
    match h : removeLoops.findIdx path state (idx - 1) with
    | some j =>
      have : j < idx := by grind only [findIdx_lt]
      ⟨removeUpTo path j, by grind only [findIdx_eq]⟩
    | none =>
      let pre := removeUpTo path (idx - 1)
      have trans := by grind only [trans]
      let path' := pre.val.push state trans
      have h := by simp [path', push, final, state, Array.back_eq_getElem]
      ⟨path', h⟩
termination_by idx

private theorem removeUpTo_initial_eq_initial :
    (removeUpTo path idx bound).val.initial = path.initial := by
  fun_induction removeUpTo
  · simp [initial, trivial]
  · simpa
  · grind [push, initial]

private theorem removeUpTo_size_le :
    (removeUpTo path idx bound).val.size ≤ idx + 1 := by
  fun_induction removeUpTo
  · simp [initial, trivial, size]
  · lia
  · grind [push]

private theorem removeUpTo_subset_states :
    let path' := removeUpTo path idx bound
    ∀ {newIdx : Nat} (_ : newIdx < path'.val.size),
      ∃ (oldIdx : Nat) (_ : oldIdx ≤ idx),
        path'.val.state newIdx = path.state oldIdx := by
  fun_induction removeUpTo
  · simp [trivial, size, initial]; grind
  · grind only
  · grind [push, removeUpTo_size_le]

private theorem removeUpTo_Simple :
    (removeUpTo path idx bound).val.Simple := by
  fun_induction removeUpTo
  · grind [trivial, initial]
  · simpa
  · grind [removeUpTo_subset_states, push, findIdx_eq_none_implies_forall_ne, final]

end removeLoops

/-
Remove all loops from a path by rebuilding the path.
-/
def removeLoops [DecidableEq α] (path : FinPath ts) : FinPath ts :=
  removeLoops.removeUpTo path path.lastIdx 

section removeLoops
variable [DecidableEq α] {path : FinPath ts}

theorem removeLoops_size_le :
    path.removeLoops.size ≤ path.size := by
  unfold removeLoops
  grind only [removeLoops.removeUpTo_size_le]

theorem removeLoops_initial_eq :
    path.removeLoops.initial = path.initial := by
  unfold removeLoops
  exact removeLoops.removeUpTo_initial_eq_initial

theorem removeLoops_final_eq :
    path.removeLoops.final = path.final := by
  grind only [removeLoops, final, Array.back_eq_getElem]

theorem removeLoops_Simple :
    path.removeLoops.Simple := by
  unfold removeLoops
  exact removeLoops.removeUpTo_Simple 

end removeLoops

set_option linter.unusedVariables false in
/--
For all finite paths, there exists a simple path between the same states
that is at most as long (by removing the loops).
-/
theorem exists_simple_path [DecidableEq α] {ts : TransSys α} :
    ∀ (path : FinPath ts),
    ∃ (path' : FinPath ts)
      (ends : path'.Between path.initial path.final)
      (simple : path'.Simple),
      path'.size ≤ path.size := by
  intro path
  exists path.removeLoops
  apply Exists.intro ?_
  apply Exists.intro ?_
  · exact removeLoops_size_le
  · exact removeLoops_Simple
  · unfold Between
    constructor
    · exact removeLoops_initial_eq
    · exact removeLoops_final_eq

set_option linter.unusedVariables false in
/--
All simple paths in a finite transition system are at most as long as the
cardinality of the domain (as any longer path must revisit states).

We show this by creating an injective mapping from path indices to states, where
the path indices have a cardinality of `path.size`.
-/
theorem finite_simple_size_le_card [Finite α] {ts : TransSys α} :
  ∀ (path : FinPath ts) (simple : path.Simple),
    path.size ≤ Nat.card α := by
  intro path simple
  rw [←Nat.card_fin path.size]
  let map : Fin path.size -> α := (path.state ·)
  apply Nat.card_le_card_of_injective map
  grind only [Function.Injective]

end FinPath

/--
A finite trace on a transition system is a finite path such that the first
state obeys the initial predicate.
-/
structure FinTrace {α : Type} (ts : TransSys α) extends FinPath ts where
  init : ts.init toFinPath.initial
