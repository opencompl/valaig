module

public import Valaig.Aig.Core
public import Valaig.Aig.Fanin
public import Valaig.Data.VarCache
public import Valaig.Data.Nullable
import Valaig.ForLean.Array
import Valaig.ForLean.Function

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

@[ext]
structure TFIWalker (aig : WFAig) (σ α : Type) (null : Data.Nullable α := by infer_instance) where
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
    (sm : stateMotive state idx (by grind)) ->
    (cm :
      ∀ var' ∈ aig.TFI var reset, ∃ valid mem,
        cacheMotive state idx (by grind) sm var' valid (cache[var']'mem)) ->
    σ × { elem : α // Data.Nullable.isSome elem }

  stepState idx var state cache valid lt sm cm :
    stateMotive (step idx var state cache valid lt sm cm).fst (idx + 1) (by grind)

  stepCache idx var state cache valid lt sm cm var' valid' mem'
    (cacheValid : cacheMotive state idx (by omega) sm var' valid' (cache[var']'mem')) :
    cacheMotive (step idx var state cache valid lt sm cm).fst (idx + 1) (by grind)
        (by apply stepState) var' valid' cache[var']

  stepCacheNew idx var state cache valid lt sm cm :
    cacheMotive (step idx var state cache valid lt sm cm).fst (idx + 1) (by grind)
      (by apply stepState) var valid (step idx var state cache valid lt sm cm).snd.val

namespace TFIWalker
variable {aig : WFAig} {σ α : Type} {null : Data.Nullable α}

@[ext]
structure State (walker : TFIWalker aig σ α null) where
  idx : Nat
  state : σ
  cache : VarCache α
  stack : Array Var

  idx_eq : idx = cache.fillSlow
  size_cache : cache.size = aig.size

  sm : walker.stateMotive state idx (by grind)

  cacheValid :
    ∀ {var} (valid : var.validIn aig), var ∈ cache ->
      walker.cacheMotive state idx (by grind [cache.fillSlow_le_size]) sm var valid cache[var]
  cacheTFI : ∀ var ∈ cache, ∀ var' ∈ aig.TFI var walker.reset, var' ∈ cache

  stackValid : ∀ var ∈ stack, var.validIn aig
  stackUncached : ∀ var ∈ stack, var ∉ cache
  stackOrdered : ∀ i j (hi : i < stack.size) (hj : j < stack.size), i < j → stack[i] > stack[j]

namespace State
variable {walker : TFIWalker aig σ α null} {s : State walker}

/--
  TODO: Investigate not requiring cache to be aig size (maybe it could be sparse, maybe it could
  only be as large as the output var).
-/
@[always_inline]
def new (walker : TFIWalker aig σ α) (var : Var) (valid : var.validIn aig := by grind) : State walker where
  idx := 0
  state := walker.init
  cache := .replicate aig.size null.null
  stack := #[var]

  idx_eq := by grind
  size_cache := by grind

  sm := walker.initState

  cacheValid := by grind
  cacheTFI := by grind

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

@[simp, grind →]
theorem idx_lt_size_of_stack {s : State walker} (h : 0 < s.stack.size) :
    s.idx < aig.size := by
  simp only [VarCache.fillSlow, s.idx_eq, ←s.size_cache, VarCache.size]
  rw [Array.countP_eq_size_filter, Array.size_filter_lt_size_iff_exists]
  have := s.stackValid s.stack.back (by grind)
  have := s.size_cache
  have := s.stackUncached s.stack.back (by grind)
  exists s.cache[s.stack.back]
  constructor
  · simp +instances [VarCache.instGetElem]
  · grind

@[always_inline]
def stepWalker (s : State walker) (var : Var)
    (h : 0 < s.stack.size := by grind)
    (var_eq : var = s.stack.back := by grind)
    (tfiCached : ∀ var' ∈ aig.TFI var walker.reset, var' ∈ s.cache := by grind) :
    State walker :=
  have := s.stackValid var (by grind)

  let res := walker.step s.idx var s.state s.cache (by grind) (by grind) s.sm <| by
    intros
    exists by grind
    exists by grind
    apply s.cacheValid
    grind [s.cacheTFI]

  {
    idx := s.idx + 1
    state := res.fst
    cache := s.cache.set var res.snd.val (lt := by grind [s.size_cache])
    stack := s.stack.pop

    idx_eq := by grind [s.idx_eq, s.stackUncached]
    size_cache := by grind [s.size_cache]
    sm := by intros; apply walker.stepState
    cacheValid := by
      intros
      simp
      split
      next heq =>
        subst heq
        apply walker.stepCacheNew
      · apply walker.stepCache
        apply s.cacheValid
        grind only [= VarCache.mem_set]

    cacheTFI := by grind [s.cacheTFI]

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

section stepWalker
variable {var : Var} {h : 0 < s.stack.size} {var_eq : var = s.stack.back}
variable {tfiCached : ∀ (var' : Var), var' ∈ aig.TFI var walker.reset → var' ∈ s.cache}

@[simp, grind =]
theorem idx_stepWalker :
    (s.stepWalker var h var_eq tfiCached).idx = s.idx + 1 := by
  rfl

@[simp]
theorem measure_lt_stepWalker :
    (s.stepWalker var h var_eq tfiCached).measure.lexLt s.measure := by
  grind [Prod.lexLt_def, measure]

grind_pattern measure_lt_stepWalker => (s.stepWalker var h var_eq tfiCached).measure, s.measure

@[simp, grind .]
theorem mem_cache_stepWalker {var' : Var} (mem : var' ∈ s.cache) :
    var' ∈ (s.stepWalker var h var_eq tfiCached).cache := by
  unfold stepWalker
  grind

@[simp, grind .]
theorem mem_stack_stepWalker {var' : Var} (mem : var' ∈ s.stack) :
    var' ∈ (s.stepWalker var h var_eq tfiCached).stack ∨
    var' ∈ (s.stepWalker var h var_eq tfiCached).cache := by
  unfold stepWalker
  by_cases h : var' = s.stack.back
  · grind
  · grind [Array.mem_iff_getElem]

@[simp, grind =]
theorem state_stepWalker :
    (s.stepWalker var h var_eq tfiCached).state =
    (walker.step s.idx var s.state s.cache (by grind [s.stackValid var (by grind)]) (by grind) s.sm  <| by
      intros
      exists by grind
      exists by grind
      apply s.cacheValid
      grind [s.cacheTFI]
    ).fst := by
  rfl

end stepWalker

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

section enqueueVar
variable {var : Var} {sized : 0 < s.stack.size} {valid : var.validIn aig}
variable {uncached : var ∉ s.cache} {ordered : var < s.stack.back}

@[simp]
theorem measure_lt_enqueueVar :
    (s.enqueueVar var sized valid uncached ordered).measure.lexLt s.measure := by
  grind [Prod.lexLt_def, measure, enqueueVar]

grind_pattern measure_lt_enqueueVar => (s.enqueueVar var sized valid uncached ordered).measure, s.measure

@[simp, grind =]
theorem cache_enqueueVar :
    (s.enqueueVar var sized valid uncached ordered).cache = s.cache := by
  grind [enqueueVar]

@[simp, grind .]
theorem mem_stack_enqueueVar {var'} (mem : var' ∈ s.stack) :
    var' ∈ (s.enqueueVar var sized valid uncached ordered).stack := by
  grind [enqueueVar]

@[simp, grind =]
theorem state_enqueueVar :
    (s.enqueueVar var sized valid uncached ordered).state = s.state := by
  rfl

@[simp, grind =]
theorem idx_enqueueVar :
    (s.enqueueVar var sized valid uncached ordered).idx = s.idx := by
  rfl

end enqueueVar

@[always_inline, specialize walker]
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
          have := s.cacheTFI rst.var
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

    have := s.cacheTFI lhs.var
    have := s.cacheTFI rhs.var
    s.stepWalker var

theorem step_eq (s : State walker) (h := by grind) :
    (∃ var' valid uncached ordered, (s.step h) = s.enqueueVar var' h valid uncached ordered) ∨
    (∃ var_eq tfiCached, (s.step h) = s.stepWalker (s.stack.back h) h var_eq tfiCached) := by
  fun_cases step <;> grind

@[simp]
theorem step_lt_enqueueVar h :
    (s.step h).measure.lexLt s.measure := by
  cases step_eq s <;> grind

@[simp, grind .]
theorem mem_cache_step {var : Var} (mem : var ∈ s.cache) h :
    var ∈ (s.step h).cache := by
  cases step_eq s <;> grind

@[simp, grind .]
theorem mem_stack_step {var : Var} (mem : var ∈ s.stack) :
    var ∈ (s.step h).stack ∨ var ∈ (s.step h).cache := by
  cases step_eq s <;> grind

@[always_inline, specialize walker reset step]
private def walk.rebuildWalker (walker : TFIWalker aig σ α null)
    (reset : Bool) step
    (hreset : walker.reset = reset := by grind)
    (hstep : walker.step = step := by grind) :
    TFIWalker aig σ α null := by
  let step' idx var state cache valid lt sm cm :=
    step idx var state cache valid lt sm (by rw [hreset]; exact cm)

  apply TFIWalker.mk walker.stateMotive walker.cacheMotive reset walker.init walker.initState step'
  · simp only [step', ←hreset, ←hstep]
    exact walker.stepCache
  · simp only [step', ←hreset, ←hstep]
    exact walker.stepCacheNew
  · simp only [step', ←hreset, ←hstep]
    exact walker.stepState

@[simp, grind =]
private theorem walk.rebuildWalker_eq reset step hreset hstep :
    rebuildWalker walker reset step hreset hstep = walker := by
  fun_cases rebuildWalker
  apply TFIWalker.ext (by rfl) (by rfl) (by simp [hreset]) (by rfl)
  repeat' (
    apply hfunext
    · simp only [←hreset]
    focus
      try simp only [←hreset]
      intro _ _ heq
      subst heq
  )
  grind only

@[always_inline, specialize walker]
private def walk.rebuildState (s : State walker)
    (idx : Nat) (state : σ) (cache : VarCache α) (stack : Array Var)
    (hidx : s.idx = idx := by grind)
    (hstate : s.state = state := by grind)
    (hcache : s.cache = cache := by grind)
    (hstack : s.stack = stack := by grind) :
    State walker := by
  apply State.mk idx state cache stack
  <;> simp only [←hidx, ←hstate, ←hcache, ←hstack]
  · refine s.cacheValid
  · refine s.cacheTFI
  · refine s.stackValid
  · refine s.stackUncached
  · refine s.stackOrdered
  · refine s.idx_eq
  · refine s.size_cache
  · refine s.sm

@[simp, grind =]
private theorem walk.rebuildState_eq (s : State walker) idx state cache stack hidx hstate hcache hstack :
    rebuildState s idx state cache stack hidx hstate hcache hstack = s := by
  fun_cases rebuildState
  grind only [State]

private def walk.castState {walker'} (s : State walker) (h : walker = walker' := by grind) : State walker' :=
  cast (by simp only [h]) s

@[simp, grind =]
private theorem walk.castState_heq {walker'} (s : State walker) (h : walker = walker') :
    castState s h ≍ s := by
  fun_cases castState
  grind only

private theorem walk.motive_castState {walker' β} (s : State walker) (h : walker = walker')
    (motive : (walker : TFIWalker aig σ α null) → (s : State walker) → β) :
    motive walker' (castState s h) = motive walker s := by
  grind only [= castState_heq]

@[simp, grind =]
private theorem walk.castState_step {walker'} (s : State walker) (h : walker = walker') h0 :
    (castState s h).step h0 = castState (s.step (by grind)) h  := by
  grind only [= castState_heq]

open walk in
/--
  We optimize the performance by unboxing the arguments and repopulating them into
  the walker/state with each call.
-/
@[always_inline, specialize walker]
def walk (s : State walker) : State walker :=
  go s walker.reset walker.step s.idx s.state s.cache s.stack
where
  @[specialize walker reset step]
  go (s : State walker)
    (reset : Bool) step
    (idx : Nat) (state : σ) (cache : VarCache α) (stack : Array Var)
    (hreset : walker.reset = reset := by grind)
    (hstep : walker.step = step := by grind)
    (hidx : s.idx = idx := by grind)
    (hstate : s.state = state := by grind)
    (hcache : s.cache = cache := by grind)
    (hstack : s.stack = stack := by grind) :
    State walker :=
  if _ : stack.size = 0 then
    rebuildState s idx state cache stack
  else
    let walker' := rebuildWalker walker reset step
    let s' : State walker' := castState (rebuildState s idx state cache stack)
    let s' : State walker := castState (s'.step)
    go s' reset step s'.idx s'.state s'.cache s'.stack
  termination_by s.measure
  decreasing_by
    simp only [Prod.lex_def, rebuildState_eq, castState_step, walk.motive_castState]
    apply step_lt_enqueueVar

@[always_inline]
def walkSlow (s : State walker) : State walker :=
  if _ : s.stack.size = 0 then
    s
  else
    walkSlow s.step
termination_by s.measure
decreasing_by
  rw [Prod.lex_def]
  apply step_lt_enqueueVar

@[simp, grind =]
theorem walk_eq_walkSlow {s : State walker} :
    s.walk = s.walkSlow := by
  unfold walk
  fun_induction walkSlow
  <;> unfold walk.go
  <;> grind

@[simp, grind .]
theorem mem_cache_walkSlow {var : Var} (mem : var ∈ s.cache) :
    var ∈ s.walkSlow.cache := by
  fun_induction walkSlow
  <;> grind

@[simp, grind .]
theorem mem_cache_walkSlow_of_mem_stack {var : Var} (mem : var ∈ s.stack) :
    var ∈ s.walkSlow.cache := by
  fun_induction walkSlow
  <;> grind

theorem walk.stateInduction {s : State walker}
    {inv : σ -> (idx : Nat) -> idx ≤ aig.size -> Prop}
    (invInit : inv s.state s.idx s.idx_le_size)
    (invStep :
      ∀ (s : State walker) var valid lt le cm,
        inv s.state s.idx s.idx_le_size →
        inv (walker.step s.idx var s.state s.cache valid lt s.sm cm).fst (s.idx + 1) le) :
    inv s.walk.state s.walk.idx s.walk.idx_le_size := by
  simp only [State.walk_eq_walkSlow]
  fun_induction State.walkSlow
  · grind [State.walkSlow]
  next s h ih =>
    unfold State.walkSlow
    simp only [h, ↓reduceDIte]
    apply ih
    rcases State.step_eq s with (_ | ⟨_, _, h⟩)
    · grind
    · rw [h]
      simp only [State.state_stepWalker, State.idx_stepWalker]
      apply invStep
      apply invInit


end State

/--
  Iterate over all variables in the TFI of an node in topological order.

  TODO: Support reusing the cache for further entrypoints.
-/
@[inline, specialize walker]
def walk {null} (walker : TFIWalker aig σ α null) (var : Var) (valid : var.validIn aig := by grind) : (σ × Nat) × VarCache α :=
  let res := (State.new walker var).walk
  ((res.state, res.idx), res.cache)

variable {walker : TFIWalker aig σ α null} {var : Var} (valid : var.validIn aig)

@[simp, grind .]
theorem mem_cache_walk :
    var ∈ (walker.walk var valid).snd := by
  rw [walk, State.walk_eq_walkSlow]
  apply State.mem_cache_walkSlow_of_mem_stack
  grind [State.new]

@[simp, grind →]
theorem mem_cache_walk_of_mem_tfi {var'} (mem : var' ∈ aig.TFI var walker.reset) :
    var' ∈ (walker.walk var valid).snd := by
  apply State.cacheTFI
  · exact mem_cache_walk valid
  · exact mem

@[simp]
theorem idx_walk_le_size :
    (walker.walk var valid).fst.snd ≤ aig.size := by
  apply State.idx_le_size

grind_pattern idx_walk_le_size => (walker.walk var valid).fst.snd

@[simp, grind =]
theorem size_cache_walk :
    (walker.walk var valid).snd.size = aig.size := by
  apply State.size_cache

@[simp, grind! .]
theorem stateMotive_walk :
    walker.stateMotive (walker.walk var valid).fst.fst (walker.walk var valid).fst.snd (by grind) := by
  apply State.sm

@[simp]
theorem cacheMotive_walk {var'} (mem : var' ∈ (walker.walk var valid).snd) valid' :
    walker.cacheMotive (walker.walk var valid).fst.fst (walker.walk var valid).fst.snd (by grind)
      (by apply stateMotive_walk) var' valid' (walker.walk var valid).snd[var'] := by
  apply State.cacheValid
  apply mem

grind_pattern cacheMotive_walk => (walker.walk var valid).snd[var']

theorem stateInduction
    {inv : σ -> (idx : Nat) -> idx ≤ aig.size -> Prop}
    (invInit : inv walker.init 0 (by grind))
    (invStep :
      ∀ idx var state cache valid lt sm cm,
        inv (walker.step idx var state cache valid lt sm cm).fst (idx + 1) (by omega)) :
    inv (walker.walk var valid).fst.fst (walker.walk var valid).fst.snd (by grind) := by
  apply State.walk.stateInduction
  · apply invInit
  · intros
    apply invStep

end TFIWalker

end Valaig.Aig
