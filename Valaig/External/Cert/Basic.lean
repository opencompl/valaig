module

public import Valaig.Aig
import Valaig.Transform.Unroll
import Valaig.External.Sat.Std

public section
namespace Valaig.Cert
open Aig
variable {aig : WFAig}

theorem unreachable_of_simple_induction (invariant : Lit)
    (init : ∀ assign, ⟦aig, invariant, assign⟧s0)
    (consec : ∀ assign, ⟦aig, invariant, assign⟧c0 → ⟦aig, invariant, assign⟧c1) :
    aig.Unreachable invariant.invert := by
  sorry

theorem unreachable_of_relative_induction (bad invariant : Lit)
    (init : ∀ assign, ⟦aig, invariant, assign⟧s0)
    (consec : ∀ assign, ⟦aig, invariant, assign⟧c0 → ⟦aig, invariant, assign⟧c1)
    (imp : ∀ assign, ⟦aig, invariant, assign⟧c0 → !⟦aig, bad, assign⟧c0) :
  aig.Unreachable bad := by
  intro assign frame
  have := unreachable_of_simple_induction invariant init consec assign frame
  grind [denoteS_eq_denoteC_assignNext]

structure Checker where
  aig : WFAig
  initBad : Lit
  consecBad : Lit
  impBad : Lit

  hinit : initBad.validIn aig := by grind
  hconsec : consecBad.validIn aig := by grind
  himp : impBad.validIn aig := by grind

attribute [simp, grind .] Checker.hinit Checker.hconsec Checker.himp

namespace Checker

def new (aig : WFAig) (bad : Lit) (invariant : Lit)
    (hbad : bad.validIn aig := by grind) (hinvariant : invariant.validIn aig := by grind) : Checker :=
  let (eq:=_) (aig, cache, _) := Transform.unroll aig
  let (eq:=_) (aig, notImp) := aig.addAnd bad invariant

  -- Init: Invariant should hold initially
  let initBad := invariant.invert

  -- Consecution: Whenever the invariant holds in one cycle, it should also hold in the next
  let (eq:=_) (aig, consecBad) := aig.addAnd invariant (cache.mapLit invariant.invert)

  -- Implication: Whenever invariant holds, bad shouldn't hold
  let impBad := notImp

  { aig, initBad, consecBad, impBad }

def initAig (checker : Checker) : Std.Sat.AIG.Entrypoint LeafIdx :=
  Sat.toStd checker.aig true checker.initBad

def consecAig (checker : Checker) : Std.Sat.AIG.Entrypoint LeafIdx :=
  Sat.toStd checker.aig false checker.consecBad

def impAig (checker : Checker) : Std.Sat.AIG.Entrypoint LeafIdx :=
  Sat.toStd checker.aig false checker.impBad

theorem unreachable_of {bad : Lit} {invariant : Lit} {hbad hinv}
    (hinit : (new aig bad invariant hbad hinv).initAig.Unsat)
    (hconsec : (new aig bad invariant hbad hinv).consecAig.Unsat)
    (himp : (new aig bad invariant hbad hinv).impAig.Unsat) :
    aig.Unreachable bad := by
  apply unreachable_of_relative_induction bad invariant
  · simp only [initAig, Sat.Unsat_toStd_reset, new] at hinit
    intro assign
    grind [denoteS_zero_eq_assign_zero, @hinit (assign · 0)]
  · simp only [consecAig, new, WFAig.snd_addAnd, WFAig.raw_fst_addAnd, Sat.Unsat_toStd_not_reset,
      Unsat] at hconsec
    intro assign
    simp (disch := grind) only [denoteC_addAnd,
      denoteC_mono (@mono_addAnd (Transform.unroll aig).fst bad invariant),
      denoteC_mono (Transform.mono_unroll aig)] at hconsec
    replace hconsec := hconsec (Transform.unroll.assignMap assign (Transform.unroll aig).snd.snd)
    grind [denoteC_of_assign_eq, Transform.unroll.assignMap]
  · simp only [impAig, new, Sat.Unsat_toStd_not_reset, Unsat, denoteC_eq] at himp
    intro assign
    grind [himp assign]

end Checker

end Valaig.Cert
