module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finite.Card

public section
namespace Valaig.FinMC

/-
A theory of Model Checking for finite-state transition systems.
-/

/--
A transition system over some domain α has predicates defining the
initial states and the transition relation between states.
-/
structure TransSys (α : Type) where
  init : α -> Prop
  trans : α -> α -> Prop

variable {α : Type} {ts : TransSys α}

namespace TransSys

/--
An uninitialised transition system is one that admits all initial states.
-/
def Uninitialised (ts : TransSys α) : Prop :=
  ∀ {state : α}, ts.init state

/--
Replace the initial state predicate with one allowing all initial states
-/
def uninit (ts : TransSys α) : TransSys α :=
  { ts with init _ := true }

@[simp, grind! .]
theorem uninit_Uninitialised : ts.uninit.Uninitialised := by
  simp [uninit, Uninitialised]

@[simp, grind =]
theorem uninit_trans_eq : ts.uninit.trans = ts.trans := by
  simp only [uninit]

end TransSys

/--
A finite path on a transition system is a finite sequence of states (stored as
an array) such that each pair are related by the transition relation.
-/
structure FinPath {α : Type} (ts : TransSys α) where
  states : Array α
  sized : states.size > 0

  trans :
    ∀ {i : Nat} (_ : i < states.size - 1),
      ts.trans states[i] states[i + 1]

attribute [local grind! .] FinPath.sized
attribute [local grind .] FinPath.trans

namespace FinPath
variable {path : FinPath ts}

def size (path : FinPath ts) : Nat :=
  path.states.size

@[simp, grind! .]
theorem zero_lt_size :
    0 < path.size := by
  grind [size]

instance : NeZero (path.size) := by
  grind [neZero_iff, size]

def state (path : FinPath ts) (idx : Nat) (lt_size : idx < path.size := by grind) : α :=
  path.states[idx]

/--
The index of `final`.
-/
@[simp]
abbrev lastIdx (path : FinPath ts) : Nat :=
  path.size - 1

/--
The initial state of a path is the state with the lowest index.
-/
def initial (path : FinPath ts) : α :=
  path.states[0]'path.sized

@[simp, grind =]
theorem initial_def :
    path.initial = path.state 0 := by
  simp [initial, state]

/--
The final state of a path is the state with the greatest index.
-/
def final (path : FinPath ts) : α :=
  path.states.back (by grind only [path.sized])

@[simp, grind =]
theorem final_def :
    path.final = path.state path.lastIdx := by
  simp [final, Array.back_eq_getElem, state, size]

/--
A path between two states is a path such that the initial and final states
are these states.
-/
@[simp, grind]
def Between (path : FinPath ts) (initial final : α) : Prop :=
  path.initial = initial ∧ path.final = final

/--
Construct a trivial path from a single state.
-/
def trivial (state : α) : FinPath ts :=
  {
    states := #[state],
    sized := by simp
    trans := by simp
  }

section trivial
variable {state : α}

@[simp, grind =]
theorem size_trivial :
    (trivial state : FinPath ts).size = 1 := by
  simp [trivial, size]

@[simp, grind =]
theorem state_zero_trivial :
    (trivial state : FinPath ts).state 0 = state := by
  simp [trivial, FinPath.state]

@[simp, grind =]
theorem state_trivial {idx : Nat} (eq_zero : idx = 0) :
    (trivial state : FinPath ts).state idx = state := by
  simp [eq_zero]

@[simp]
theorem initial_trivial :
    (trivial state : FinPath ts).initial = state := by
  simp

@[simp]
theorem final_trivial :
    (trivial state : FinPath ts).final = state := by
  grind

end trivial

/--
Add a new state to the end of the path that obeys the transition relation.
-/
def push (path : FinPath ts) (state : α) (trans : ts.trans path.final state := by grind) : FinPath ts :=
  {
    states := path.states.push state,
    sized := by simp,
    trans := by grind [FinPath.trans, size, state]
  }

section push
variable {state : α} {trans : ts.trans path.final state}

@[simp, grind =]
theorem size_push :
    (path.push state trans).size = path.size + 1 := by
  simp [push, size]

@[simp]
theorem state_push_lt {idx : Nat} (h : idx < path.size) :
    (path.push state trans).state idx = path.state idx := by
  grind [push, size, state]

@[simp]
theorem state_push_eq :
    (path.push state trans).state path.size = state:= by
  simp [push, size, FinPath.state]

@[grind =]
theorem state_push {idx : Nat} (h : idx < (path.push state trans).size) :
    (path.push state trans).state idx =
    if h : idx < path.size then
      path.state idx
    else
      state := by
  simp [push, size, FinPath.state, Array.getElem_push]

@[simp]
theorem initial_push :
    (path.push state trans).initial = path.initial := by
  grind

@[simp]
theorem final_push :
    (path.push state trans).final = state := by
  grind

end push

/--
Extract the subsequence of the path from `start` to `stop` exclusive.
-/
def extract (path : FinPath ts) (start stop : Nat)
    (le_stop : start < stop := by grind)
    (le_size : stop ≤ path.size := by grind) : FinPath ts :=
  {
    states := path.states.extract start stop,
    sized := by simp_all [size],
    trans := by grind
  }

section extract
variable {start stop : Nat} (le_stop : start < stop) (le_size: stop ≤ path.size)

@[simp, grind =]
theorem size_extract :
    (path.extract start stop le_stop le_size).size = stop - start := by
  grind [extract, size]

@[simp, grind =]
theorem state_extract {i : Nat} (h : i < (path.extract start stop le_stop le_size).size) :
    (path.extract start stop le_stop le_size).state i = path.state (start + i) := by
  simp [extract, state]

@[simp]
theorem initial_extract :
    (path.extract start stop le_stop le_size).initial = path.state start := by
  simp_all

@[simp]
theorem final_extract :
    (path.extract start stop le_stop le_size).final = path.state (stop - 1) := by
  grind

end extract

/--
Truncate the path to size `size`.
-/
def truncate (path : FinPath ts) (size : Nat)
    (zero_lt : 0 < size := by grind)
    (le_size : size ≤ path.size := by grind) : FinPath ts :=
  path.extract 0 size

section truncate
variable {size : Nat} (zero_lt : 0 < size) (le_size : size ≤ path.size)

@[local grind =]
theorem truncate_eq_extract :
    path.truncate size zero_lt le_size = path.extract 0 size := by
  simp [truncate]

@[simp, grind =]
theorem size_truncate :
    (path.truncate size zero_lt le_size).size = size := by
  grind

@[simp, grind =]
theorem state_truncate {i : Nat} (h : i < size) :
    (path.truncate size zero_lt le_size).state i = path.state i := by
  grind

@[simp]
theorem initial_truncate :
    (path.truncate size zero_lt le_size).initial = path.initial := by
  simp_all

@[simp]
theorem final_truncate :
    (path.truncate size zero_lt le_size).final = path.state (size - 1) := by
  simp_all

end truncate

/--
For every path there is a shorter path with the same initial state.
-/
theorem exists_shorter_path_initial_eq {size : Nat} (leSize : size ≤ path.size) (gtZero : size > 0) :
    ∃ (path' : FinPath ts) (_ : path'.size = size),
      path'.initial = path.initial := by
  exists path.truncate size
  grind 

/--
For every path there is a shorter path with the same final state.
-/
theorem exists_shorter_path_final_eq {size : Nat} (leSize : size ≤ path.size) (gtZero : size > 0) :
    ∃ (path' : FinPath ts) (_ : path'.size = size),
      path'.final = path.final := by
    exists path.extract (path.size - size) path.size
    grind

/--
A path is simple if it does not visit the same state twice.
-/
@[grind]
def Simple (path : FinPath ts) : Prop :=
  ∀ {i j : Nat} (_ : i < path.size) (_ : j < path.size),
    i ≠ j →
      path.state i ≠ path.state j

section simple
variable {state : α} {trans : ts.trans path.final state}

@[simp, grind .]
theorem Simple_trivial :
    (trivial state : FinPath ts).Simple := by
  grind

@[simp, grind .]
theorem Simple_push_of_Simple (simple : path.Simple)
    (new : ∀ {idx} (_ : idx < path.size), path.state idx ≠ state) :
    (path.push state trans).Simple := by
  grind

end simple

namespace removeLoops
variable [DecidableEq α] {idx : Nat} {lt_size : idx < path.size}
variable {state : α}

/--
Returns the greatest index in `path` that is equal to `state` and at most `idx`,
if one exists.
-/
private def findIdx [DecidableEq α] (path : FinPath ts)
    (state : α) (idx : Nat) (lt_size : idx < path.size := by lia) : Option Nat :=
  if path.state idx = state then
    some idx
  else if h : idx = 0 then
    none
  else
    findIdx path state (idx - 1)

private theorem findIdx_lt :
    match findIdx path state idx lt_size with
    | some n => n ≤ idx
    | _ => True := by
  fun_induction findIdx
  · simp
  · simp
  · grind only [Option.all_eq_true]

private theorem findIdx_eq :
    match _ : findIdx path state idx lt_size with
    | some n =>
      path.state n (by grind only [findIdx_lt]) = state
    | _ => True := by
  fun_induction findIdx
  <;> grind only [findIdx]

private theorem findIdx_eq_none_implies_forall_ne :
    (h : findIdx path state idx lt_size = none) →
      ∀ {idx' : Nat} (_ : idx' ≤ idx), path.state idx' ≠ state := by
  fun_induction findIdx
  · simp
  · grind only
  · grind only

private def removeUpTo
    [DecidableEq α] (path : FinPath ts) (idx : Nat)
    (lt_size : idx < path.size := by grind) :
    { path' : FinPath ts // path'.final = path.state idx } :=
  if hidx : idx = 0 then
    ⟨.trivial path.initial, by simp_all⟩
  else
    let state := path.state idx
    match h : removeLoops.findIdx path state (idx - 1) with
    | some j =>
      have : j < idx := by grind only [findIdx_lt]
      ⟨removeUpTo path j, by grind only [findIdx_eq]⟩
    | none =>
      let pre := removeUpTo path (idx - 1)
      have trans := by grind [trans, size, state]
      let path' := pre.val.push state trans
      have h := by simp [path', state]
      ⟨path', h⟩
termination_by idx

private theorem removeUpTo_initial_eq_initial :
    (removeUpTo path idx lt_size).val.initial = path.initial := by
  fun_induction removeUpTo
  · simp
  · simpa
  · grind

private theorem removeUpTo_size_le :
    (removeUpTo path idx lt_size).val.size ≤ idx + 1 := by
  fun_induction removeUpTo
  · simp
  · lia
  · grind

private theorem removeUpTo_subset_states :
    let path' := removeUpTo path idx lt_size
    ∀ {newIdx : Nat} (_ : newIdx < path'.val.size),
      ∃ (oldIdx : Nat) (_ : oldIdx ≤ idx),
        path'.val.state newIdx = path.state oldIdx := by
  fun_induction removeUpTo
  <;> grind [removeUpTo]

private theorem findIdx_eq_none_implies_removeUpTo_ne_state :
    findIdx path state idx lt_size = none →
    let path' := removeUpTo path idx lt_size
    ∀ {newIdx : Nat} (_ : newIdx < path'.val.size),
      path'.val.state newIdx ≠ state := by
  intro h _ _ size
  rcases removeUpTo_subset_states size with ⟨_, ⟨newSize, _⟩⟩
  have := findIdx_eq_none_implies_forall_ne h newSize
  grind only

private theorem removeUpTo_Simple :
    (removeUpTo path idx lt_size).val.Simple := by
  fun_induction removeUpTo
  · grind
  · simpa
  next ih1 ih2 =>
    apply Simple_push_of_Simple
    · assumption
    · assumption
    · grind only [findIdx_eq_none_implies_removeUpTo_ne_state]

end removeLoops

/-
Remove all loops from a path by rebuilding the path.
-/
def removeLoops [DecidableEq α] (path : FinPath ts) : FinPath ts :=
  removeLoops.removeUpTo path path.lastIdx 

section removeLoops
variable [DecidableEq α] {path : FinPath ts}

@[simp]
theorem removeLoops_size_le :
    path.removeLoops.size ≤ path.size := by
  unfold removeLoops
  grind only [removeLoops.removeUpTo_size_le]

grind_pattern removeLoops_size_le => path.removeLoops.size

@[simp, grind =]
theorem removeLoops_initial_eq :
    path.removeLoops.initial = path.initial := by
  unfold removeLoops
  exact removeLoops.removeUpTo_initial_eq_initial

@[simp, grind =]
theorem removeLoops_final_eq :
    path.removeLoops.final = path.final := by
  grind only [removeLoops, final_def]

@[simp, grind! .]
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
theorem exists_simple_path [DecidableEq α] (path : FinPath ts) :
    ∃ (path' : FinPath ts)
      (ends : path'.Between path.initial path.final)
      (simple : path'.Simple),
      path'.size ≤ path.size := by
  exists path.removeLoops
  grind

set_option linter.unusedVariables false in
/--
All simple paths in a finite transition system are at most as long as the
cardinality of the domain (as any longer path must revisit states).

We show this by creating an injective mapping from path indices to states, where
the path indices have a cardinality of `path.size`.
-/
@[simp]
theorem size_le_card_of_Finite_Simple [Finite α] (simple : path.Simple) :
    path.size ≤ Nat.card α := by
  rw [←Nat.card_fin path.size]
  let map : Fin path.size -> α := (path.state ·)
  apply Nat.card_le_card_of_injective map
  grind [Function.Injective]

grind_pattern size_le_card_of_Finite_Simple => Finite α, path.Simple, path.size

end FinPath

/--
A finite trace on a transition system is a finite path such that the first
state obeys the initial predicate.
-/
structure FinTrace {α : Type} (ts : TransSys α) extends FinPath ts where
  init : ts.init toFinPath.initial := by grind

attribute [grind! .] FinTrace.init

abbrev FinTrace.path (trace : FinTrace ts) :=
  trace.toFinPath

namespace TransSys

def Reachable (ts : TransSys α) (pred : α -> Prop) : Prop :=
  ∃ (trace : FinTrace ts), pred trace.final

def Safe (ts : TransSys α) (pred : α -> Prop) : Prop :=
  ∀ (trace : FinTrace ts), pred trace.final

theorem Safe_iff_not_reachable_not :
    ts.Safe pred ↔ ¬ts.Reachable (¬pred ·) := by
  simp [Safe, Reachable]

set_option linter.unusedVariables false in
def SafeUpTo (ts : TransSys α) (pred : α -> Prop) (bound : Nat) :=
  ∀ (trace : FinTrace ts) (lt_bound : trace.size ≤ bound),
    pred trace.final

variable {pred : α -> Prop}

theorem Safe_iff_forall_SafeUpTo :
    ts.Safe pred ↔ ∀ {n : Nat}, ts.SafeUpTo pred n := by
  unfold Safe SafeUpTo
  aesop

theorem Safe_iff_SafeUpTo_card_of_finite [Finite α] [DecidableEq α] :
    ts.Safe pred ↔ ts.SafeUpTo pred (Nat.card α) := by
  rw [Safe_iff_forall_SafeUpTo]
  unfold SafeUpTo
  constructor
  · grind
  · intro h _ trace _
    have : trace.final = (FinTrace.mk trace.removeLoops).final := by
      rw [FinPath.removeLoops_final_eq]
    rw [this]
    apply h
    simp

end TransSys
