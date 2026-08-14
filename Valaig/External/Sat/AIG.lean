module

public import Std.Sat.AIG.Basic
public import Valaig.Aig.Core
public import Std.Sat.AIG.Cached
import Std.Sat.AIG.CachedLemmas

public section
namespace Valaig.Sat
open Aig
open Std.Sat.AIG

/--
  A wrapper for Std.Sat.AIG that removes the dependent typing, making it easier to reason about.
-/
@[local grind]
structure AIG where
  aig : Std.Sat.AIG LeafIdx

namespace AIG
variable {aig : AIG} {assign : LeafIdx -> Bool}

@[inline]
def empty : AIG :=
  { aig := .empty }

@[simp]
private theorem ref_hgate {aig : Std.Sat.AIG LeafIdx} {ref : aig.Ref} :
    ref.gate < aig.decls.size :=
  ref.hgate

grind_pattern ref_hgate => ref.gate, aig.decls.size

@[local simp, local grind]
def contains (aig : AIG) (var : Var) : Prop :=
  var.idx < aig.aig.decls.size

@[simp, grind .]
theorem contains_constant :
    aig.contains .constant := by
  simp [aig.aig.hzero]

@[inline, local simp, local grind]
def entrypoint (aig : AIG) (lit : Lit) (h : aig.contains lit.var := by grind) : Entrypoint LeafIdx :=
  ⟨aig.aig, lit.toRef aig.aig h⟩

@[local simp, local grind]
def denote (aig : AIG) (lit : Lit) (assign : LeafIdx -> Bool) (h : aig.contains lit.var := by grind) : Bool :=
  Std.Sat.AIG.denote assign (aig.entrypoint lit)

@[simp, grind =]
theorem denote_false :
    aig.denote Lit.false assign = false := by
  simp [Lit.toRef, Std.Sat.AIG.denote_idx_false aig.aig.hconst]

@[simp, grind =]
theorem denote_mapTo {lit new : Lit} h  :
    aig.denote (lit.mapTo new) assign h = (lit.inverted ^^ aig.denote new assign) := by
  simp [Lit.toRef]
  by_cases hn : new.inverted
  <;> by_cases hl : lit.inverted
  <;> simp [hn, hl]
  <;> grind only [Std.Sat.AIG.denote_not_invert]

@[simp, grind =]
theorem denote_entrypoint {assign} {lit : Lit} h :
    Std.Sat.AIG.denote assign (aig.entrypoint lit h) =
      aig.denote lit assign := by
  rfl

@[inline]
def mkAtomCached (aig : AIG) (atom : LeafIdx) : AIG × Lit :=
  let res := aig.aig.mkAtomCached atom
  ({ aig with aig := res.aig }, .ofRef res.ref)

section mkAtomCached
variable {atom : LeafIdx}
attribute [local simp, local grind] mkAtomCached
attribute [local simp, local grind! .] mkAtomCached_le_size

@[simp, grind .]
theorem mem_mkAtomCached {var : Var} (h : aig.contains var) :
    (aig.mkAtomCached atom).fst.contains var := by
  grind

@[simp, grind .]
theorem mem_mkAtomCached_self :
    (aig.mkAtomCached atom).fst.contains (aig.mkAtomCached atom).snd.var := by
  grind

@[simp, grind =]
theorem denote_mkAtomCached {lit : Lit} (h : aig.contains lit.var) :
    (aig.mkAtomCached atom).fst.denote lit assign = aig.denote lit assign := by
  generalize hentry : aig.entrypoint lit = entry
  grind [Lit.toRef,
    show aig = { aig with aig := entry.aig } by grind,
    show lit = .ofRef entry.ref by grind,
    Std.Sat.AIG.LawfulOperator.denote_input_entry (f := Std.Sat.AIG.mkAtomCached)]

@[simp, grind =]
theorem denote_mkAtomCached_self :
    (aig.mkAtomCached atom).fst.denote (aig.mkAtomCached atom).snd assign = assign atom := by
  simp

end mkAtomCached

@[inline]
def mkGateCached (aig : AIG) (lhs rhs : Lit)
    (hl : aig.contains lhs.var := by grind) (hr : aig.contains rhs.var := by grind) : AIG × Lit :=
  let res := aig.aig.mkGateCached <| .mk (lhs.toRef aig.aig hl) (rhs.toRef aig.aig hr)
  ({ aig with aig := res.aig }, .ofRef res.ref)

section mkGateCached
variable {lhs rhs : Lit} {hl : aig.contains lhs.var} {hr : aig.contains rhs.var}
attribute [local simp, local grind] mkGateCached
attribute [local simp, local grind! .] mkGateCached_le_size

@[simp, grind .]
theorem mem_mkGateCached {var : Var} (h : aig.contains var) :
    (aig.mkGateCached lhs rhs hl hr).fst.contains var := by
  grind

@[simp, grind .]
theorem mem_mkGateCached_self :
    (aig.mkGateCached lhs rhs hl hr).fst.contains (aig.mkGateCached lhs rhs hl hr).snd.var := by
  grind

@[simp, grind =]
theorem denote_mkGateCached {lit : Lit} (h : aig.contains lit.var) :
    (aig.mkGateCached lhs rhs hl hr).fst.denote lit assign = aig.denote lit assign := by
  generalize hentry : aig.entrypoint lit = entry
  grind [Lit.toRef,
    show aig = { aig with aig := entry.aig } by grind,
    show lit = .ofRef entry.ref by grind,
    Std.Sat.AIG.LawfulOperator.denote_input_entry (f := Std.Sat.AIG.mkGateCached)]

@[simp, grind =]
theorem denote_mkGateCached_self :
    (aig.mkGateCached lhs rhs hl hr).fst.denote (aig.mkGateCached lhs rhs hl hr).snd assign =
      ((aig.denote lhs assign) && (aig.denote rhs assign)) := by
  simp

end mkGateCached

end AIG
end Valaig.Sat
