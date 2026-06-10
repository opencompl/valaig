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

    -- Try to simp two input first - this catches things like const prop that appear with just two
    -- inputs
    match _ : TwoLevelSimp.twoInput lhs rhs with
    | some lit => (aig.rewriteAnd var lit lit, lit)
    | none =>

    match _ : aig[lhs.var], _ : aig[rhs.var] with
    | .and l0 l1, .and r0 r1 =>
      -- We don't map l0/l1/r0/r1 as they should have been updated by the cache already
      match  _ : TwoLevelSimp.simplifyAnd lhs rhs l0 l1 r0 r1 with
      | .lit l => (aig.rewriteAnd var l l, l)
      | .and l r => (aig.rewriteAnd var l r, var)
    | _, _ => (aig.rewriteAnd var lhs rhs, var)

  stepState := by
    intros
    simp only
    (repeat' split)
    · rw [Id.run, WFAig.raw_rewriteAnd, var_validIn, nodes_rewriteAnd] <;> grind
    · rw [Id.run, WFAig.raw_rewriteAnd, var_validIn, nodes_rewriteAnd] <;> grind
    · rw [Id.run, WFAig.raw_rewriteAnd, var_validIn, nodes_rewriteAnd] <;> grind
    · rw [Id.run, WFAig.raw_rewriteAnd, var_validIn, nodes_rewriteAnd] <;> grind
    · grind

  stepCache := by grind
  stepCacheNew := by
    intros
    simp only
    (repeat' split)
    · rw [Id.run]; grind
    · rw [Id.run]; grind
    · rw [Id.run]; grind
    · rw [Id.run]; grind
    · grind

end twoLevelSimp

def twoLevelSimp (aig : WFAig) : WFAig :=
  (twoLevelSimp.walker aig).walk aig (by grind [twoLevelSimp.walker]) |>.fst

end Valaig.Transform
