module

public import Valaig.Aig

public section
namespace Valaig.Transform
open Aig

namespace unroll

@[always_inline]
private def walker (old : Aig) : old.CachingForwardsWalker Aig Lit where
  stateMotive aig size le := aig.WF ∧ old ≤ aig
  cacheMotive aig size le sm var lt lit := lit.validIn aig

  step var aig cache valid size sm cm :=
    match _ : aig[var] with
    | .false       => (aig, .false)
    | .and lhs rhs => let (eq:=_) (aig, var) := aig.addAndRaw (cache.mapLit lhs) (cache.mapLit rhs)
                      (aig, var)
    | .input _     => let (eq:=_) (aig, idx) := aig.addInput; (aig, idx.getVar aig)
    | .latch idx   => (aig, idx.getNext aig)

  stepState := by intros; split <;> grind
  stepCache := by intros; split <;> grind
  stepCacheNew := by intros; split <;> grind

end unroll

/--
  Unroll the Aig by one time step. The second timestep is appended onto the existing circuit
  as a combinational function.

  TODO: Strashing whilst unrolling
-/
def unroll (aig : Aig) (wf : aig.WF := by grind) : Aig × Data.VarCache Lit :=
  (unroll.walker aig).walk aig (by grind [unroll.walker])

end Valaig.Transform
