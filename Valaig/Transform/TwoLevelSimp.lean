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

    have : ∀ {var' : Var} (h : var' < var), cache[var'].validIn aig := by grind [mem_nodes_iff]
    let (eq:=heq) res := TwoLevelSimp.simplifyAnd lhs rhs (aig.asAnd lhs.var) (aig.asAnd rhs.var)
    have := TwoLevelSimp.var_simplifyAnd (· < var) heq

    match _ : res with
    | .lit lit => (aig.rewriteAnd var lit lit, lit)
    | .and l r => (aig.rewriteAnd var l r, var)

  stepState := by
    intro var
    intros
    split
    · simp only [Id.run, var_validIn]
      split
      next heq =>
        have := TwoLevelSimp.var_simplifyAnd_lit (· ≠ var) heq (by grind) (by grind) (by grind) (by grind)
        rw [WFAig.raw_rewriteAnd, nodes_rewriteAnd] <;> grind
      next heq =>
        have := TwoLevelSimp.var_simplifyAnd_and (· ≠ var) heq (by grind) (by grind) (by grind) (by grind)
        rw [WFAig.raw_rewriteAnd, nodes_rewriteAnd] <;> grind
    · grind

  stepCache := by grind
  stepCacheNew := by
    intro var
    intros
    split
    · simp only [Id.run]
      split
      next heq =>
        have := TwoLevelSimp.var_simplifyAnd_lit (·.idx < var.idx + 1) heq (by grind) (by grind) (by grind) (by grind)
        grind
      next heq =>
        have := TwoLevelSimp.var_simplifyAnd_and (·.idx < var.idx + 1) heq (by grind) (by grind) (by grind) (by grind)
        grind
    · grind

end twoLevelSimp

def twoLevelSimp (aig : WFAig) : WFAig :=
  (twoLevelSimp.walker aig).walk aig (by grind [twoLevelSimp.walker]) |>.fst

end Valaig.Transform
