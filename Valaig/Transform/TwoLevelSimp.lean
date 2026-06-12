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

  step var aig cache valid size sm cm := Id.run do
    let (eq:=_) .and lhs rhs := aig[var] | return (aig, var)

    -- Map through cache to make sure we have optimized versions
    let lhs := cache.mapLit lhs
    let rhs := cache.mapLit rhs

    match  heq : TwoLevelSimp.simplifyAnd lhs rhs (aig.asAnd lhs.var) (aig.asAnd rhs.var) with
    | .lit lit =>
      have := TwoLevelSimp.var_simplifyAnd (· < var) heq
      (aig.rewriteAnd var lit lit, lit)
    | .and l r =>
      have := TwoLevelSimp.var_simplifyAnd (· < var) heq
      (aig.rewriteAnd var l r , var)

  stepState := by
    intro var
    intros
    simp only
    split
    · rw [Id.run, var_validIn];
      split
      next heq =>
        have := TwoLevelSimp.var_simplifyAnd (· ≠ var) heq
        rw [WFAig.raw_rewriteAnd, nodes_rewriteAnd] <;> grind
      next heq =>
        have := TwoLevelSimp.var_simplifyAnd (· ≠ var) heq
        rw [WFAig.raw_rewriteAnd, nodes_rewriteAnd] <;> grind
    · grind

  stepCache := by grind
  stepCacheNew := by
    intro var
    intros
    simp only
    split
    · split
      next heq =>
        have := TwoLevelSimp.var_simplifyAnd (·.idx < var.idx + 1) heq
        simp only [Id.run]; grind
      next heq =>
        have := TwoLevelSimp.var_simplifyAnd (·.idx < var.idx + 1) heq
        simp only [Id.run]; grind
    · grind

end twoLevelSimp

def twoLevelSimp (aig : WFAig) : WFAig :=
  (twoLevelSimp.walker aig).walk aig (by grind [twoLevelSimp.walker]) |>.fst

end Valaig.Transform
