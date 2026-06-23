module

public import Valaig.Aig.Core
public import Valaig.Data.VarCache
public import Valaig.Data.Nullable
import Valaig.ForLean.Array

public section
namespace Valaig.Aig

open Data (VarCache)

structure ForwardsWalker (aig : Aig) (σ : Type) where
  motive : σ -> (idx : Nat) -> idx ≤ aig.size -> Prop

  init : σ

  motiveInit : motive init 0 (by omega)

  step :
    (var : Var) -> (state : σ) ->
    (valid : var.validIn aig) ->
    motive state var.idx (by grind) ->
    σ

  motiveStep var state valid m :
    motive (step var state valid m) (var.idx + 1) (by grind)

namespace ForwardsWalker
variable {aig : Aig} {σ : Type}
attribute [local grind .] ForwardsWalker.motiveStep ForwardsWalker.motiveInit

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
def walk (walker : aig.ForwardsWalker σ) : σ :=
  walk.go walker walker.step aig.iter walker.init

variable (walker : aig.ForwardsWalker σ)

private theorem walk.induction_go {step it state} valid eq
    {inv : σ -> (idx : Nat) -> idx ≤ aig.size -> Prop}
    (invInit : inv state (aig.iterVal it).idx (by grind))
    (invStep : (var : Var) -> (state : σ) -> (valid : var.validIn aig) ->
      (motive : walker.motive state var.idx (by grind)) ->
      inv (walker.step var state valid motive) (var.idx + 1) (by grind)) :
    inv (walk.go walker step it state valid eq) aig.size (by grind) := by
  fun_induction go <;> grind

theorem induction {inv : σ -> (idx : Nat) -> idx ≤ aig.size -> Prop}
    (invInit : inv walker.init 0 (by grind))
    (invStep : (var : Var) -> (state : σ) -> (valid : var.validIn aig) ->
      (motive : walker.motive state var.idx (by grind)) ->
      inv (walker.step var state valid motive) (var.idx + 1) (by grind)) :
    inv walker.walk aig.size (by grind) := by
  apply walk.induction_go <;> grind

@[simp, grind! .]
theorem motive_walk :
    walker.motive walker.walk aig.size (by grind) := by
  apply induction <;> grind

end ForwardsWalker

structure CachingForwardsWalker (aig : Aig) (σ α : Type) where
  stateMotive : σ -> (idx : Nat) -> idx ≤ aig.size -> Prop
  cacheMotive :
    (state : σ) -> (idx : Nat) -> (le : idx ≤ aig.size) -> stateMotive state idx le ->
    (var : Var) -> var.idx < idx -> α -> Prop

  init : σ

  initState : stateMotive init 0 (by omega)

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
def walk (walker : aig.CachingForwardsWalker σ α) : σ × VarCache α :=
  walk.go walker walker.step aig.iter walker.init (.emptyWithCapacity aig.maxVar) (sm := by grind [walker.initState])

variable (walker : aig.CachingForwardsWalker σ α)

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
    walker.walk.snd.size = aig.size := by
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
    (invInit : inv walker.init 0 (by grind))
    (invStep : (var : Var) -> (state : σ) -> (cache : VarCache α) -> (valid : var.validIn aig) ->
      (size : cache.size = var.idx) -> (sm : _) -> (cm : _) ->
      inv (walker.step var state cache valid size sm cm).fst (var.idx + 1) (by grind)) :
    inv walker.walk.fst aig.size (by grind) := by
  apply walk.stateInduction_go <;> grind

@[simp, grind! .]
theorem stateMotive_walk :
    walker.stateMotive walker.walk.fst aig.size (by grind) := by
  apply stateInduction <;> grind [walker.stepState, walker.initState]

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
    inv walker.walk.fst aig.size (by grind) (by grind)
      var lt walker.walk.snd[var] := by
  apply walk.cacheInduction_go
  · grind
  · apply invStep
  · apply invStepNew

@[simp, grind! .]
theorem cacheMotive_walk var lt :
    walker.cacheMotive
      walker.walk.fst aig.size (by grind) (by grind)
      var lt walker.walk.snd[var] := by
  apply cacheInduction
  · grind [walker.stepCache]
  · grind [walker.stepCacheNew]

end CachingForwardsWalker

structure COIWalker (aig : WFAig) (σ α : Type) (null : Data.Nullable α := by infer_instance) where
  stateMotive : (state : σ) -> (idx : Nat) -> idx ≤ aig.size -> Prop
  cacheMotive :
    (state : σ) -> (idx : Nat) -> (le : idx ≤ aig.size) -> stateMotive state idx le ->
    (var : Var) -> var.validIn aig -> α -> Prop

  reset : Bool

  init : σ

  initState : stateMotive init 0 (by omega)

  step :
    (idx : Nat) -> (var : Var) -> (state : σ) -> (cache : VarCache α) ->
    (valid : var.validIn aig) -> (lt : idx < aig.size) ->
    (cacheAnds : ∀ {lhs rhs}, aig[var] = .and lhs rhs -> lhs.var ∈ cache ∧ rhs.var ∈ cache) ->
    (cacheResets : reset ->
      ∀ {idx rst} (h : aig[var] = .latch idx), idx.getReset aig = some rst -> rst.var ∈ cache) ->
    (cacheValid :
      ∀ {var' : Var} {lhs rhs} (valid : var'.validIn aig),
        var' ∈ cache -> aig[var'] = .and lhs rhs -> lhs.var ∈ cache ∧ rhs.var ∈ cache) ->
    (sm : stateMotive state idx (by grind)) ->
    (cm : ∀ {var'} (valid : var'.validIn aig) (mem : var' ∈ cache),
      cacheMotive state idx (by grind) sm var' valid cache[var']) ->
    σ × { elem : α // Data.Nullable.isSome elem }

  stepState idx var state cache valid lt cacheAnds cacheResets cacheValid sm cm :
    stateMotive (step idx var state cache valid lt cacheAnds cacheResets cacheValid sm cm).fst (idx + 1) (by grind)

  stepCache idx var state cache valid lt cacheAnds cacheResets cacheValid sm cm :
    ∀ {var'} (valid' : var'.validIn aig) (mem : var' ∈ cache),
      cacheMotive (step idx var state cache valid lt cacheAnds cacheResets cacheValid sm cm).fst (idx + 1) (by grind)
        (by apply stepState) var' valid' cache[var']

  stepCacheNew idx var state cache valid lt cacheAnds cacheResets cacheValid sm cm :
    cacheMotive (step idx var state cache valid lt cacheAnds cacheResets cacheValid sm cm).fst (idx + 1) (by grind)
      (by apply stepState) var valid (step idx var state cache valid lt cacheAnds cacheResets cacheValid sm cm).snd.val

namespace COIWalker
variable {aig : WFAig} {σ α : Type} [null : Data.Nullable α]

structure State (walker : COIWalker aig σ α) where
  idx : Nat
  state : σ
  cache : VarCache α
  stack : Array Var

  idx_eq : idx = cache.fillSlow
  size_cache : cache.size = aig.size

  cacheValid :
    ∀ {var' : Var} {lhs rhs} (valid : var'.validIn aig),
      var' ∈ cache -> aig[var'] = .and lhs rhs -> lhs.var ∈ cache ∧ rhs.var ∈ cache

  sm : walker.stateMotive state idx (by grind)
  cm :
    ∀ {var'} (valid : var'.validIn aig), var' ∈ cache ->
      walker.cacheMotive state idx (by grind [cache.fillSlow_le_size]) sm var' valid cache[var']

  stackValid : ∀ var ∈ stack, var.validIn aig
  stackUncached : ∀ var ∈ stack, var ∉ cache
  stackOrdered : ∀ i j (hi : i < stack.size) (hj : j < stack.size), i < j → stack[i] > stack[j]

namespace State
variable {walker : COIWalker aig σ α} {s : State walker}

/--
  TODO: Investigate not requiring cache to be aig size (maybe it could be sparse, maybe it could
  only be as large as the output var).
-/
@[always_inline]
def new (walker : COIWalker aig σ α) (var : Var) (valid : var.validIn aig := by grind) : State walker where
  idx := 0
  state := walker.init
  cache := .replicate aig.size null.null
  stack := #[var]

  idx_eq := by grind
  size_cache := by grind

  cacheValid := by grind

  sm := walker.initState
  cm := by grind

  stackValid := by grind
  stackUncached := by grind
  stackOrdered := by grind

@[simp]
theorem idx_le_size : 
    s.idx ≤ aig.size := by
  grind [s.idx_eq, s.size_cache]

grind_pattern idx_le_size => s.idx, aig.size

def measure (s : State walker) : Nat × Var :=
  (aig.size - s.idx, s.stack.back?.getD .constant)

@[always_inline]
def stepWalker (s : State walker) (var : Var)
    (h : 0 < s.stack.size := by grind)
    (var_eq : var = s.stack.back := by grind)
    (cacheAnds : ∀ {lhs rhs},
      aig[var]'(by grind [s.stackValid]) = .and lhs rhs -> lhs.var ∈ s.cache ∧ rhs.var ∈ s.cache := by grind)
    (cacheResets : walker.reset ->
      ∀ {idx rst} (h : aig[var]'(by grind [s.stackValid]) = .latch idx), idx.getReset aig = some rst -> rst.var ∈ s.cache := by grind) :
    State walker :=
  have := s.stackValid var (by grind)

  have : s.idx < aig.size := by
    simp only [VarCache.fillSlow, s.idx_eq, ←s.size_cache, VarCache.size]
    rw [Array.countP_eq_size_filter, Array.size_filter_lt_size_iff_exists]
    exists s.cache[var]'(by grind [s.size_cache])
    constructor
    · simp +instances [VarCache.instGetElem]
    · grind [s.stackUncached var (by grind)]

  let res := walker.step s.idx var s.state s.cache
    (by grind) (by grind) (by grind) (by grind) s.cacheValid s.sm s.cm
  {
    idx := s.idx + 1
    state := res.fst
    cache := s.cache.set var res.snd.val
    stack := s.stack.pop

    idx_eq := by grind [s.idx_eq, s.stackUncached]
    size_cache := by grind [s.size_cache]
    cacheValid := by grind [s.cacheValid]
    sm := by intros; apply walker.stepState
    cm := by
      intros
      simp
      split
      next heq =>
        subst heq
        apply walker.stepCacheNew
      · apply walker.stepCache
        · grind only [= VarCache.mem_set]

    stackValid := by grind [s.stackValid]
    stackUncached := by
      intro var mem
      rw [Array.mem_pop_iff_getElem] at mem
      rcases mem with ⟨i, h, mem⟩
      have := s.stackUncached var
      have := s.stackOrdered i (s.stack.size - 1)
      grind
    stackOrdered := by grind [s.stackOrdered]
  }

@[simp, grind =]
theorem idx_stepWalker var h var_eq cacheAnds cacheResets :
    (s.stepWalker var h var_eq cacheAnds cacheResets).idx = s.idx + 1 := by
  rfl

@[simp]
theorem measure_lt_stepWalker var h var_eq cacheAnds cacheResets :
    (s.stepWalker var h var_eq cacheAnds cacheResets).measure.lexLt s.measure := by
  grind [Prod.lexLt_def, measure]

grind_pattern measure_lt_stepWalker => (s.stepWalker var h var_eq cacheAnds cacheResets).measure, s.measure

@[always_inline]
def enqueueVar (s : State walker) (var : Var)
  (sized : 0 < s.stack.size := by grind)
  (valid : var.validIn aig := by grind)
  (uncached : var ∉ s.cache := by grind)
  (ordered : var < s.stack.back := by grind) : State walker :=
  { s with
    stack := s.stack.push var

    stackValid := by grind [s.stackValid]
    stackUncached := by grind [s.stackUncached]
    stackOrdered := by
      intro i j hi hj ord
      rw [Array.getElem_push]
      split
      · rw [Array.getElem_push]
        split
        · grind [s.stackOrdered]
        · by_cases i = s.stack.size - 1
          · grind
          · suffices s.stack[i] > s.stack.back by grind
            grind [s.stackOrdered]
      · rw [Array.getElem_push_lt] <;> grind
  }

@[simp]
theorem measure_lt_enqueueVar var sized valid uncached ordered :
    (s.enqueueVar var sized valid uncached ordered).measure.lexLt s.measure := by
  grind [Prod.lexLt_def, measure, enqueueVar]

grind_pattern measure_lt_enqueueVar => (s.enqueueVar var sized valid uncached ordered).measure, s.measure

@[always_inline]
def step (s : State walker) (h : 0 < s.stack.size := by grind) : State walker :=
  let var := s.stack.back
  have : var.validIn aig := by grind [s.stackValid]

  have := s.size_cache

  match _ : aig[var] with
  | .false | .input _ => s.stepWalker var
  | .latch idx =>
    if _ : !walker.reset then
      s.stepWalker var
    else
      match _ : idx.getReset aig with
      | none => s.stepWalker var
      | some rst =>
        let rstVal := s.cache[rst.var]
        if _ : null.isNull rstVal then
          s.enqueueVar rst.var
        else
          s.stepWalker var
  | .and lhs rhs =>
    let lhsVal := s.cache[lhs.var]
    if _ : null.isNull lhsVal then
      s.enqueueVar lhs.var
    else

    let rhsVal := s.cache[rhs.var]
    if _ : null.isNull rhsVal then
      s.enqueueVar rhs.var
    else

    s.stepWalker var

@[simp]
theorem step_lt_enqueueVar h :
    (s.step h).measure.lexLt s.measure := by
  fun_cases step <;> grind

/-
  TODO: Try unboxing recursive args.
-/
@[always_inline]
def walk (s : State walker) : State walker :=
  if _ : s.stack.size = 0 then
    s
  else
    walk s.step
termination_by s.measure
decreasing_by
  rw [Prod.lex_def]
  apply step_lt_enqueueVar

end State

/--
  Iterate over all variables in the COI of an node in topological order.

  TODO: Support reusing the cache for further entrypoints.
-/
@[inline, specialize walker]
def walk {null} (walker : COIWalker aig σ α null) (var : Var) (valid : var.validIn aig := by grind) : σ × VarCache α :=
  let res := (State.new walker var).walk
  (res.state, res.cache)

end COIWalker

end Valaig.Aig
