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

variable {walker : aig.ForwardsWalker σ} (init : σ) (motive : walker.motive init 0 (by grind))

private theorem walk.induction_go {step it state} valid eq
    {inv : σ -> (idx : Nat) -> idx ≤ aig.size -> Prop}
    (invInit : inv state (aig.iterVal it).idx (by grind))
    (invStep : (var : Var) -> (state : σ) -> (valid : var.validIn aig) ->
      (motive : walker.motive state var.idx (by grind)) ->
      inv (walker.step var state valid motive) (var.idx + 1) (by grind)) :
    inv (walk.go walker step it state valid eq) aig.size (by grind) := by
  fun_induction go <;> grind

theorem induction {inv : σ -> (idx : Nat) -> idx ≤ aig.size -> Prop}
    (invInit : inv init 0 (by grind))
    (invStep : (var : Var) -> (state : σ) -> (valid : var.validIn aig) ->
      (motive : walker.motive state var.idx (by grind)) ->
      inv (walker.step var state valid motive) (var.idx + 1) (by grind)) :
    inv (walker.walk init motive) aig.size (by grind) := by
  apply walk.induction_go <;> grind

@[simp, grind! .]
theorem motive_walk :
    walker.motive (walker.walk init motive) aig.size (by grind) := by
  apply induction <;> grind


end ForwardsWalker

structure CachingForwardsWalker (aig : Aig) (σ α : Type) where
  stateMotive : σ -> (idx : Nat) -> idx ≤ aig.size -> Prop
  cacheMotive :
    (state : σ) -> (idx : Nat) -> (le : idx ≤ aig.size) -> stateMotive state idx le ->
    (var : Var) -> var.idx < idx -> α -> Prop

  step :
    (var : Var) -> (state : σ) -> (cache : VarCache α) ->
    (valid : var.validIn aig) -> (size : cache.size = var.idx) ->
    (sm : stateMotive state var.idx (by grind)) ->
    (cm : ∀ {var'} (h : var' < var), cacheMotive state var.idx (by grind) sm var' h cache[var']) ->
    σ × α

  stepState var state cache valid size sm cm :
    stateMotive (step var state cache valid size sm cm).fst (var.idx + 1) (by grind)

  stepCache var state cache le valid size (sm : stateMotive state var.idx le) cm :
    ∀ {var'} (h : var' < var),
      cacheMotive (step var state cache valid size sm cm).fst (var.idx + 1) (by grind) (by grind)
        var' (by grind) cache[var']

  stepCacheNew var state cache valid size sm cm :
    cacheMotive (step var state cache valid size sm cm).fst (var.idx + 1) (by grind) (by grind)
      var (by grind) (step var state cache valid size sm cm).snd

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
    (cm : ∀ {var'} (h : var' < (aig.iterVal it)), walker.cacheMotive state (aig.iterVal it).idx (by grind) sm var' (by grind) cache[var'] := by grind)
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

variable {walker : aig.CachingForwardsWalker σ α} (init : σ) (motive : walker.stateMotive init 0 (by grind))

@[simp, grind .]
private theorem walk.stateMotive_go {step it state cache} size sm cm eq :
    walker.stateMotive (walk.go walker step it state cache size sm cm eq).fst aig.size (by grind) := by
  fun_induction go <;> grind

@[simp, grind =]
private theorem walk.size_cache_go {step it state cache} size sm cm eq :
    (walk.go walker step it state cache size sm cm eq).snd.size = aig.size := by
  fun_induction go <;> grind

@[simp, grind =]
theorem size_cache_walk :
    (walker.walk init motive).snd.size = aig.size := by
  grind [walk]

private theorem walk.stateInduction_go {step it state cache} size sm cm eq
    {inv : σ -> (idx : Nat) -> idx ≤ aig.size -> Prop}
    (invInit : inv state (aig.iterVal it).idx (by grind))
    (invStep : (var : Var) -> (state : σ) -> (cache : VarCache α) -> (valid : var.validIn aig) ->
      (size : cache.size = var.idx) -> (sm : _) -> (cm : _) ->
      inv (walker.step var state cache valid size sm cm).fst (var.idx + 1) (by grind)) :
    inv (walk.go walker step it state cache size sm cm eq).fst aig.size (by grind) := by
  fun_induction go
  · grind
  next it state cache _ _ _ _ _ _ _ _ _ _ =>
    have := @invStep (aig.iterVal it) state cache (by grind) (by grind) (by grind) (by grind)
    grind

theorem stateInduction {inv : σ -> (idx : Nat) -> idx ≤ aig.size -> Prop}
    (invInit : inv init 0 (by grind))
    (invStep : (var : Var) -> (state : σ) -> (cache : VarCache α) -> (valid : var.validIn aig) ->
      (size : cache.size = var.idx) -> (sm : _) -> (cm : _) ->
      inv (walker.step var state cache valid size sm cm).fst (var.idx + 1) (by grind)) :
    inv (walker.walk init motive).fst aig.size (by grind) := by
  apply walk.stateInduction_go <;> grind

@[simp, grind! .]
theorem stateMotive_walk :
    walker.stateMotive (walker.walk init motive).fst aig.size (by grind) := by
  apply stateInduction <;> grind [walker.stepState]

private theorem walk.cacheInduction_go {step it state cache} size sm cm eq
    {inv : (state : σ) -> (idx : Nat) -> (le : idx ≤ aig.size) -> walker.stateMotive state idx le ->
      (var : Var) -> var.idx < idx -> α -> Prop}
    (invUpTo :
      ∀ {var' : Var} (h : var'.idx < (aig.iterVal it).idx),
        inv state (aig.iterVal it).idx (by grind) sm var' h cache[var'])
    (invStep : (var : Var) -> (state : σ) -> (cache : VarCache α) -> (valid : var.validIn aig) ->
      (size : cache.size = var.idx) -> (sm : _) -> (cm : _) ->
      ∀ {var' : Var} (h : var' < var),
        inv (walker.step var state cache valid size sm cm).fst (var.idx + 1) (by grind) (by grind [walker.stepState])
          var' (by grind) cache[var'])
    (invStepNew : (var : Var) -> (state : σ) -> (cache : VarCache α) -> (valid : var.validIn aig) ->
      (size : cache.size = var.idx) -> (sm : _) -> (cm : _) ->
      inv (walker.step var state cache valid size sm cm).fst (var.idx + 1) (by grind) (by grind [walker.stepState])
        var (by grind) (step var state cache valid size sm cm).snd)
    var lt :
    inv (walk.go walker step it state cache size sm cm eq).fst aig.size (by grind) (by grind)
      var lt (walk.go walker step it state cache size sm cm eq).snd[var] := by
  fun_induction go
  · unfold go
    grind only [→ VarIter.done_eq, = iterVal_iterEnd, = idx_nextVar]
  next it state cache _ _ _ _ _ _ _ step res ih =>
    unfold go
    simp only [step]
    apply ih
    simp only [VarCache.getElem_push]
    intros
    split
    · have := @invStepNew (aig.iterVal it) state cache (by grind) (by grind) (by grind) (by grind)
      grind
    · have := @invStep (aig.iterVal it) state cache (by grind) (by grind) (by grind) (by grind)
      grind

theorem cacheInduction
    {inv : (state : σ) -> (idx : Nat) -> (le : idx ≤ aig.size) -> walker.stateMotive state idx le ->
      (var : Var) -> var.idx < idx -> α -> Prop}
    (invStep : (var : Var) -> (state : σ) -> (cache : VarCache α) -> (valid : var.validIn aig) ->
      (size : cache.size = var.idx) -> (sm : _) -> (cm : _) ->
      ∀ {var' : Var} (h : var' < var),
        inv (walker.step var state cache valid size sm cm).fst (var.idx + 1) (by grind) (by grind [walker.stepState])
          var' (by grind) cache[var'])
    (invStepNew : (var : Var) -> (state : σ) -> (cache : VarCache α) -> (valid : var.validIn aig) ->
      (size : cache.size = var.idx) -> (sm : _) -> (cm : _) ->
      inv (walker.step var state cache valid size sm cm).fst (var.idx + 1) (by grind) (by grind [walker.stepState])
        var (by grind) (walker.step var state cache valid size sm cm).snd) var lt :
    inv (walker.walk init motive).fst aig.size (by grind) (by grind)
      var lt (walker.walk init motive).snd[var] := by
  apply walk.cacheInduction_go
  · grind
  · apply invStep
  · apply invStepNew

@[simp, grind! .]
theorem cacheMotive_walk var lt :
    walker.cacheMotive
      (walker.walk init motive).fst aig.size (by grind) (by grind)
      var lt (walker.walk init motive).snd[var] := by
  apply cacheInduction
  · grind [walker.stepCache]
  · grind [walker.stepCacheNew]

end CachingForwardsWalker

end Valaig.Aig
