import Std.Sat.AIG.Basic
import Std.Sat.AIG.Cached
import Std.Sat.AIG.CachedGates
import Std.Sat.AIG.CachedLemmas
import Std.Sat.AIG.CachedGatesLemmas

namespace Valaig.Aig

open Std.Sat AIG

variable {α : Type} [Hashable α] [DecidableEq α]

/--
`AIG.mkAtom` only appends a single atom to the underlying AIG.
-/
theorem mkAtom_eq_decls_push (aig : AIG α) (var : α) :
    (aig.mkAtom var).aig.decls = aig.decls.push (.atom var) := by
  simp only [mkAtom]

/--
`AIG.mkAtom` increments size by one.
-/
theorem mkAtom_size (aig : AIG α) (var : α) :
    (aig.mkAtom var).aig.decls.size = aig.decls.size + 1 := by
  simp only [mkAtom_eq_decls_push, Array.size_push]

/--
`AIG.mkAtom` returns a reference to the next element in the underlying AIG
-/
theorem mkAtom_ref_eq_decls_size (aig : AIG α) (var : α) :
    (aig.mkAtom var).ref.gate = aig.decls.size := by
  simp only [mkAtom]

/--
- `AIG.mkGate` only potentially appends gates, not atoms/constants
-/
theorem mkGate_matches_gate (aig : AIG α) {input : aig.BinaryInput} {idx : Nat}
    {hlow : idx ≥ aig.decls.size} {hhigh : idx < (aig.mkGate input).aig.decls.size} :
    ∃ (lhs rhs : Fanin), (aig.mkGate input).aig.decls[idx] = .gate lhs rhs := by
  generalize hres : (aig.mkGate input).aig.decls = res at *
  unfold mkGate at hres
  have heq : idx = aig.decls.size := by
    rw [←hres, Array.size_push] at hhigh
    exact Nat.eq_of_le_of_lt_succ hlow hhigh
  simp [←hres, heq]

theorem mkGateCached.go_matches_gate (aig : AIG α) {input : aig.BinaryInput} {idx : Nat}
    {hlow : idx ≥ aig.decls.size} {hhigh : idx < (mkGateCached.go aig input).aig.decls.size} :
    ∃ (lhs rhs : Fanin), (mkGateCached.go aig input).aig.decls[idx] = .gate lhs rhs := by
  generalize hres : (mkGateCached.go aig input).aig.decls = res at *
  have : aig.decls ≠ res := by cutsat
  dsimp only [mkGateCached, mkGateCached.go] at hres
  split at hres
  · trivial
  · split at hres <;> try trivial
    · grind only [Array.getElem_push]

/--
- `AIG.mkGateCached` only potentially appends gates, not atoms/constants
-/
theorem mkGateCached_matches_gate (aig : AIG α) {input : aig.BinaryInput} {idx : Nat}
    {hlow : idx ≥ aig.decls.size} {hhigh : idx < (aig.mkGateCached input).aig.decls.size} :
    ∃ (lhs rhs : Fanin), (aig.mkGateCached input).aig.decls[idx] = .gate lhs rhs := by
  dsimp only [mkGateCached]
  split <;> apply mkGateCached.go_matches_gate <;> trivial

/--
- `AIG.mkAndCached` only potentially appends gates, not atoms/constants
-/
theorem mkAndCached_matches_gate (idx : Nat) (aig : AIG α) (input : aig.BinaryInput)
    {hlow : idx ≥ aig.decls.size} {hhigh : idx < (aig.mkAndCached input).aig.decls.size} :
    ∃ (lhs rhs : Fanin), (aig.mkAndCached input).aig.decls[idx] = .gate lhs rhs := by
  simp_all only [mkAndCached, mkGateCached_matches_gate]

end Valaig.Aig
