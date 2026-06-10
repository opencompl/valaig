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

@[inline]
def resolveInputs (aig : WFAig) (var : Var) (valid : var.validIn aig := by grind) : Option (Lit × Lit × Lit × Lit × Lit × Lit) :=
  match _ : aig[var] with
  | .and l r =>
    match _ : aig[l.var], _ : aig[r.var] with
    | .and l0 l1, .and r0 r1 =>
      let (l, l0, l1) :=
        if l0 = l1 then
          match aig[l0.var] with
          | .and l00 l01 => (l.invert l0.inverted, l00, l01)
          | _ => (l, l0, l1)
        else
          (l, l0, l1)

      let (r, r0, r1) :=
        if r0 = r1 then
          match aig[r0.var] with
          | .and r00 r01 => (r.invert r0.inverted, r00, r01)
          | _ => (r, r0, r1)
        else
          (r, r0, r1)

      some (l, r, l0, l1, r0, r1)
    | _, _ => none
  | _ => none

@[always_inline]
private def walker (old : WFAig) : old.ForwardsWalker WFAig where
  motive aig size le := ∀ {var : Var}, var.validIn old → var.validIn aig

  step var aig valid sm := Id.run do
    let some (lhs, rhs, l0, l1, r0, r1) := resolveInputs aig var | return aig
    match TwoLevelSimp.simplifyAnd lhs rhs l0 l1 r0 r1 with
    | .lit l => return aig.rewriteAnd! var l l |>.get! |>.toWF sorry
    | .and l r => return aig.rewriteAnd! var l r |>.get! |>.toWF sorry

  motiveStep := sorry
end twoLevelSimp

def twoLevelSimp (aig : WFAig) : WFAig :=
  (twoLevelSimp.walker aig).walk aig (by grind [twoLevelSimp.walker])

end Valaig.Transform
