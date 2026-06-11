module

public import Valaig.Aig
import Valaig.Aig.TwoLevelSimp

public section
namespace Valaig.Transform
open Aig

/-!
This module applies two-level simplification at each node in the Aig. If a node can be simplified
to a single literal, it is replaced with an and-gate with two inputs the same.
-/

namespace twoLevelSimp

@[always_inline]
private def walker (old : WFAig) : old.CachingForwardsWalker WFAig Lit where
  stateMotive aig size le := ∀ {var : Var}, var.validIn old → var.validIn aig
  cacheMotive aig idx le sm var lt lit := lit.var.idx < idx

  step var aig cache valid size sm cm  := Id.run do
    let (eq:=_) .and lhs rhs := aig[var] | return (aig, var)

    -- Map through cache to make sure we have optimized versions
    let lhs := cache.mapLit lhs
    let rhs := cache.mapLit rhs

    match  _ : TwoLevelSimp.simplifyAnd lhs rhs (aig.asAnd lhs.var) (aig.asAnd rhs.var) with
    | .lit lit => (aig.rewriteAnd var lit lit (lvalid := sorry) (rvalid := sorry), lit)
    | .and l r => (aig.rewriteAnd var l r (lvalid := sorry) (rvalid := sorry), var)

  stepState := by
    intros
    simp only
    split
    · rw [Id.run, var_validIn];
      split
      · rw [WFAig.raw_rewriteAnd, nodes_rewriteAnd]
        · grind
        · sorry
        · sorry
      · rw [WFAig.raw_rewriteAnd, nodes_rewriteAnd]
        · grind
        · sorry
        · sorry
    · grind

  stepCache := by grind
  stepCacheNew := by
    intros
    simp only
    split
    · split
      · rw [Id.run]; sorry
      · rw [Id.run]; sorry
    · grind

end twoLevelSimp

def twoLevelSimp (aig : WFAig) : WFAig :=
  (twoLevelSimp.walker aig).walk aig (by grind [twoLevelSimp.walker]) |>.fst

end Valaig.Transform
