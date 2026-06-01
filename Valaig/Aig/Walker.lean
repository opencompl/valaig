module

public import Valaig.Aig.Basic
public import Valaig.Aig.Lemmas
public import Valaig.Data.VarCache

public section
namespace Valaig.Aig

open Data (VarCache)

structure ForwardsWalker (aig : Aig) (σ : Type) where
  motive : σ -> (idx : Nat) -> idx ≤ aig.size -> Prop

  step :
    (var : Var) -> (state : σ) ->
    (valid : var.validIn aig) ->
    motive state var.idx (by grind) ->
    σ

  motiveStep var state valid m :
    motive (step var state valid m) (var.idx + 1) (by grind)

namespace ForwardsWalker
variable {aig : Aig} {σ : Type}
attribute [local grind .] ForwardsWalker.motiveStep

/--
  Inner loop of the walker. This does not actually depend on the `walker` parameter at runtime,
  instead using `step` which should be a copy of `walker.step`. This causes the compiler to
  more eagerly inline the construction of the `step` function, preventing it being passed as a
  callback.
-/
@[specialize walker step]
private def walk.go (walker : aig.ForwardsWalker σ) step (it : aig.Iter) (state : σ)
    (valid : walker.motive state (aig.iterVal it).idx (by grind) := by grind)
    (eq : step = walker.step := by grind) : σ :=
  match it.step with
  | .done _ => state
  | .yield it' var _ => go walker step it' (step var state (by grind) (by grind)) (by rw [eq]; grind)
termination_by it.finitelyManySteps

/--
  Iterate over all variables in the Aig in order, modifying an arbitrary state along the way.
-/
@[inline, specialize walker]
def walk (walker : aig.ForwardsWalker σ) (init : σ) (motive : walker.motive init 0 (by grind) := by grind) : σ :=
  walk.go walker walker.step aig.iter init

end ForwardsWalker

structure CachingForwardsWalker (aig : Aig) (σ α : Type) where
  stateMotive : σ -> (idx : Nat) -> idx ≤ aig.size -> Prop
  cacheMotive :
    {state : σ} -> {idx : Nat} -> {le : idx ≤ aig.size} -> stateMotive state idx le ->
    (var : Var) -> var.idx < idx -> α -> Prop

  step :
    (var : Var) -> (state : σ) -> (cache : VarCache α) ->
    (valid : var.validIn aig) -> (size : cache.size = var.idx) ->
    (sm : stateMotive state var.idx (by grind)) ->
    (cm : ∀ {var'} (h : var' < var), cacheMotive sm var' h cache[var']) ->
    σ × α

  stepState var state cache valid size sm cm :
    stateMotive (step var state cache valid size sm cm).fst (var.idx + 1) (by grind)

  stepCache var state cache le valid size (sm : stateMotive state var.idx le) cm :
    ∀ {var'} (h : var' < var),
      cacheMotive (stepState var state cache valid size sm cm) var' (by grind)
        cache[var']

  stepCacheNew var state cache valid size sm cm :
    cacheMotive (stepState var state cache valid size sm cm) var (by grind)
      (step var state cache valid size sm cm).snd

namespace CachingForwardsWalker
variable {aig : Aig} {σ α : Type}

/--
  Inner loop of the walker. This does not actually depend on the `walker` parameter at runtime,
  instead using `step` which should be a copy of `walker.step`. This causes the compiler to
  more eagerly inline the construction of the `step` function, preventing it being passed as a
  callback.
-/
@[specialize walker step]
private def walk.go (walker : aig.CachingForwardsWalker σ α) step (it : aig.Iter) (state : σ) (cache : VarCache α)
    (size : cache.size = (aig.iterVal it).idx := by grind)
    (sm : walker.stateMotive state (aig.iterVal it).idx (by grind) := by grind)
    (cm : ∀ {var'} (h : var' < (aig.iterVal it)), walker.cacheMotive sm var' (by grind) cache[var'] := by grind)
    (eq : step = walker.step := by grind) : σ × VarCache α :=
  match it.step with
  | .done _ => (state, cache)
  | .yield it' var _ =>
    let res := step var state cache (by grind) (by grind) (by grind) (by grind)
    go walker step it' res.fst (cache.push res.snd)
      (sm := by subst res; rw [eq]; grind [walker.stepState])
      (cm := by subst res; simp only [eq]; have := @walker.stepCacheNew; grind [walker.stepCache])
termination_by it.finitelyManySteps

/--
  Iterate over all variables in the Aig in order, modifying an arbitrary state along the way.
-/
@[inline, specialize walker]
def walk (walker : aig.CachingForwardsWalker σ α) (init : σ) (motive : walker.stateMotive init 0 (by grind) := by grind) : σ × VarCache α :=
  walk.go walker walker.step aig.iter init (.emptyWithCapacity aig.maxVar)

end CachingForwardsWalker

end Valaig.Aig
