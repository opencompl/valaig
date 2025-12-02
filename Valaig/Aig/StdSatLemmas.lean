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
@[simp, grind! .]
theorem mkAtom_eq_decl_push (aig : AIG α) (var : α) :
    (aig.mkAtom var).aig.decls = aig.decls.push (.atom var) := by
  simp [mkAtom]

/--
`AIG.mkAtom` returns a reference to the next element in the underlying AIG
-/
@[simp, grind! .]
theorem mkAtom_ref_eq_decl_size (aig : AIG α) (var : α) :
    (aig.mkAtom var).ref.gate = aig.decls.size := by
  simp [mkAtom]

/--
- `AIG.mkGateCached` only potentially appends gates, not atoms/constants
-/
@[simp, grind! .]
theorem mkGateCached_matches_gate (idx : Nat) (aig : AIG α) (input : aig.BinaryInput)
    {hlow : idx ≥ aig.decls.size} {hhigh : idx < (aig.mkGateCached input).aig.decls.size} :
    (aig.mkGateCached input).aig.decls[idx] matches .gate _ _ := by
  simp only [mkGateCached, mkGateCached.go]
  grind

attribute [simp, grind! .] mkGateCached_decl_eq
attribute [simp, grind! .] mkGateCached_le_size

/--
- `AIG.mkAndCached` only potentially appends gates, not atoms/constants
-/
@[simp, grind! .]
theorem mkAndCached_matches_gate (idx : Nat) (aig : AIG α) (input : aig.BinaryInput)
    {hlow : idx ≥ aig.decls.size} {hhigh : idx < (aig.mkAndCached input).aig.decls.size} :
    (aig.mkAndCached input).aig.decls[idx] matches .gate _ _ := by
  simp_all [mkAndCached]

attribute [simp, grind! .] mkAndCached_decl_eq
attribute [simp, grind! .] mkAndCached_le_size

end Valaig.Aig
