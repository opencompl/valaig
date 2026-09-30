module

public import Valaig.Aig
import Valaig.External.Sat.AIG
public import Valaig.Data.Memo

namespace Valaig.Sat
open Aig

namespace toStd

@[simp, grind unfold]
abbrev walker.info (aig : WFAig) (reset : Bool) : Data.Memo.VisitorInfo Var Lit AIG where
  lt := (· < ·)
  keyInv var := var.validIn aig
  valInv std _ var _ lit :=
    ∃ (h : std.contains lit.var),
      ∀ {assign},
        if reset then
          std.denote lit assign = ⟦aig, var, fun idx _ => assign idx⟧sv0
        else
          std.denote lit assign = ⟦aig, var, fun idx _ => assign idx⟧cv0

open Data.Memo.ActionM in
@[always_inline]
def walker (aig : WFAig) (reset : Bool) : Data.Memo.Visitor (walker.info aig reset) :=
  fun std var => do
    let rec @[always_inline] map (lit : Lit) (valid : lit.var < var := by grind) :
        Data.Memo.ActionM _ _ _ { l : Lit // std.contains l.var } := do
      let new ← get lit.var
      return ⟨lit.mapTo new, by grind⟩

    match _ : aig[var] with
    | .false => .just .false
    | .and lhs rhs => return std.mkGateCached (←map lhs) (←map rhs)
    | .input idx   => return std.mkAtomCached idx
    | .latch idx   =>
      if _ : reset then
        match _ : idx.getReset aig with
        | none     => return std.mkAtomCached idx
        | some lit => .just (←map lit)
      else
        return std.mkAtomCached idx

variable {reset : Bool}

instance instWF {aig : WFAig} : Data.Memo.WFVisitor (walker aig reset) where
  stateInv := by grind
  valInv std var hki hsi query _ walk hvi := by
    intro motive
    apply walker.fun_cases_unfolding (motive := motive)
    <;> simp only [motive, walker.map]
    <;> intros
    <;> rename_i hpure hsi
    <;> revert hpure
    <;> simp [Option.get_unattach, Option.isSome_bind, Option.any_eq_true_iff_get]
    <;> grind
  cachePreservation std root hroot var val hki hsi hci _ _ walk hci' := by
    intro motive
    apply walker.fun_cases_unfolding (motive := motive)
    <;> simp only [motive]
    <;> intros
    <;> rename_i hpure hsi
    <;> revert hpure
    <;> simp [Option.get_unattach, Option.isSome_bind, Option.any_eq_true_iff_get]
    <;> grind

end toStd

public section

open Data Memo in
def toStd (aig : WFAig) (reset : Bool) (entry : Lit) (valid : entry.validIn aig := by grind) : Std.Sat.AIG.Entrypoint LeafIdx :=
  let w := dfsHashWalker (toStd.walker aig reset)
  let s := w.new .empty
  let (eq:=_) (s', lit) := w.visit s entry.var
  (w.state s').entrypoint (entry.mapTo lit) (by have := w.valInv; grind)

section toStd
variable {aig : WFAig} {reset : Bool} {entry : Lit} {valid : entry.validIn aig}

@[simp, grind =]
theorem denote_toStd_reset {assign} :
    Std.Sat.AIG.denote assign (toStd aig true entry valid) =
      ⟦aig, entry, fun idx _ => assign idx⟧s0 := by
  fun_cases toStd
  next wf s _ _ _ =>
    have := wf.valInv s entry.var
    grind

@[simp, grind =]
theorem denote_toStd_not_reset {assign} :
    Std.Sat.AIG.denote assign (toStd aig false entry valid) =
      ⟦aig, entry, fun idx _ => assign idx⟧c0 := by
  fun_cases toStd
  next wf s _ _ _ =>
    have := wf.valInv s entry.var
    grind

@[simp, grind =]
theorem Unsat_toStd_reset :
    (toStd aig true entry valid).Unsat ↔
      ∀ {assign : LeafIdx -> Bool}, ⟦aig, entry, fun idx _ => assign idx⟧s0 = false := by
  simp [Std.Sat.AIG.Entrypoint.Unsat, Std.Sat.AIG.UnsatAt]

@[simp, grind =]
theorem Unsat_toStd_not_reset :
    (toStd aig false entry valid).Unsat ↔ aig.Unsat entry := by
  simp [Unsat_iff, Std.Sat.AIG.Entrypoint.Unsat, Std.Sat.AIG.UnsatAt]

end toStd
end
end Valaig.Sat
