module

public import Std.Data.HashMap
public import Valaig.Data.FiniteOrder
public import Valaig.Data.VarCache
public import Valaig.ForLean.Prod
public import Valaig.Data.Refs
import Valaig.ForLean.Array

public section
namespace Valaig.Data.Memo

/-
  In this file we use the following meanings for letters:
  - α : cache key
  - β : cache value
  - σ : walker state
  - μ : user state
  - γ : monad return types
-/
variable {α β σ μ γ : Type} {a root : α} {b : β} {usr : μ}

/--
  An invariant on the user state in the walker.
-/
@[expose, implicit_reducible]
def StateInv (μ : Type) := μ -> Prop

/--
  An invariant on a value in the cache, indexed by the user state.
-/
@[expose, implicit_reducible]
def ValInv (si : StateInv μ) (α β : Type) :=
  {s : μ} -> si s -> α -> β -> Prop

@[expose, implicit_reducible]
def Query (σ β : Type) (lt : α -> α -> Prop) (root : α) :=
  σ -> (a : α) -> lt a root -> Option β

variable {lt : α -> α -> Prop} {si : StateInv μ} {ci : ValInv si α β}

@[expose, implicit_reducible, local grind]
def Query.respects (query : Query σ β lt root) (p : α -> β -> Prop) (s : σ) :=
  ∀ {k h v}, query s k h = some v → p k v

@[grind .]
theorem Query.respects_get {query : Query σ β lt root} {p : α -> β -> Prop} {s : σ}
      (hrespects : query.respects p s) (k : α) hlt h :
    p k ((query s k hlt).get h) := by
  grind

@[expose, implicit_reducible]
def Enqueue (query : Query σ β lt root) :=
  (s : σ) -> (a : α) -> (h : lt a root) -> query s a h = none -> { s' : σ // query s' = query s }

@[simp]
theorem Enqueue.respects_enqueue {query : Query σ β lt root} {enqueue : Enqueue query}
    {p : α -> β -> Prop} {s : σ} {a : α} {h heq} :
    query.respects p (enqueue s a h heq) ↔ query.respects p s := by
  grind

/--
  This captures a relationship between states that is true if they have had at least one
  and potentially multiple variables enqueued.
-/
inductive Enqueue.reach {query : Query σ β lt root} (enq : Enqueue query) : σ -> σ -> Prop
| init {s a} (hlt := by grind) (hq := by grind) : enq.reach s (enq s a hlt hq)
| trans {s s' a} (hs : enq.reach s s') (hlt := by grind) (hq := by grind) : enq.reach s (enq s' a hlt hq)

theorem Enqueue.reach.rel {query : Query σ β lt root} {enq : Enqueue query} {p : σ -> σ -> Prop} {s s'}
    (h : enq.reach s s')
    (rel : ∀ s a hlt hq, p s (enq s a hlt hq))
    (trans : ∀ a b c, p a b → p b c → p a c) :
    p s s' := by
  induction h <;> grind

section Action
variable {query : Query σ β lt root} {enq : Enqueue query}

/--
  A valid memo action either produces a value without modifying the state, or enqueues indices
  onto the walker state.
-/
inductive Action (usr : μ) (enq : Enqueue query) (γ : Type) : σ -> σ -> Type
| pure {s s'} (val : γ) (heq : s' = s := by grind): Action usr enq γ s s'
| enqueued {s s'} (usr' : μ) (heq : usr' = usr := by grind) (h : enq.reach s s' := by grind) : Action usr enq γ s s'

@[ext, grind ext]
structure ActionState (hsi : si usr) (ci : ValInv si α β) (enq : Enqueue query) (s : σ) (γ : Type) where
  state : σ
  hvi : query.respects (ci hsi) state
  action : Action usr enq γ s state

@[expose, implicit_reducible]
def ActionM (hsi : si usr) (ci : ValInv si α β) (enq : Enqueue query) (γ : Type) :=
  (s : σ) -> query.respects (ci hsi) s -> ActionState hsi ci enq s γ

variable {hsi : si usr} {s s' : σ}

namespace ActionState
variable {action : ActionState hsi ci enq s γ}

@[expose]
def value? (action : ActionState hsi ci enq s γ) : Option γ :=
  match _ : action.action with
  | .pure val _ => val
  | .enqueued _ _ _ => none

@[simp, grind .]
theorem value?_of_pure {v : γ} {heq} (hact : action.action = .pure v heq) :
    action.value? = v := by
  grind [value?]

end ActionState

namespace ActionM
open ActionState

@[always_inline]
instance : Monad (ActionM hsi ci enq) where
  pure x s hvi := ⟨s, hvi, .pure x⟩
  bind x f s hvi :=
    let a := x s hvi
    match _ : a.action with
    | .pure val heq => cast (by grind only) (f val a.state (by grind))
    | .enqueued usr heq h => { a with action := .enqueued usr heq }

variable {hvi : query.respects (ci hsi) s}

@[simp]
theorem value?_dite {c : Prop} [Decidable c] {a : c -> ActionM hsi ci enq γ} {b : ¬c -> ActionM hsi ci enq γ} :
    ((dite c a b) s hvi).value? =
      dite c
        (fun h => (a h s hvi).value?)
        (fun h => (b h s hvi).value?) := by
  grind

@[local simp, local grind =]
theorem bind_eq {δ : Type} {a : ActionM hsi ci enq δ} {b : δ -> ActionM hsi ci enq γ} :
  (a >>= b) s hvi =
    let va := a s hvi
    match _ : va.action with
    | .enqueued _ _ _   => ⟨va.state, va.hvi, .enqueued usr rfl (by grind)⟩
    | .pure val _ =>
      let vb := b val s hvi
      match _ : vb.action with
      | .enqueued _ _ _ => ⟨vb.state, vb.hvi, .enqueued usr rfl (by grind)⟩
      | .pure val _     => ⟨s, hvi, .pure val⟩ := by
  simp only [bind]
  grind only

@[simp, grind =]
theorem value?_pure {val : γ} :
    ((pure val : ActionM hsi ci enq _) s hvi).value? = val := by
  rfl

@[simp, grind =]
theorem value?_bind {δ : Type} {a : ActionM hsi ci enq δ} {b : δ -> ActionM hsi ci enq γ} :
    ((a >>= b) s hvi).value? =
      (a s hvi).value? >>= (fun x => (b x s hvi).value?) := by
  grind [value?]

/--
  Try to lookup a single value from the cache, enqueuing it to be processed before returning
  to this node if it is not found.
-/
@[always_inline, specialize query enq]
def get (a : α) (ha : lt a root := by grind) : ActionM hsi ci enq { val : β // ci hsi a val } :=
  fun s hvi =>
    match _ : query s a ha with
    | some v => ⟨s, hvi, .pure ⟨v, by grind⟩⟩
    | none => ⟨enq s a (by grind) (by grind), by grind, .enqueued usr rfl .init⟩

@[simp, grind =]
theorem value?_get {a : α} (ha : lt a root) :
    ((get a ha (enq := enq)) s hvi).value? = (query s a ha).attachWith _ (by grind) := by
  simp only [get]
  split
  next heq => simp [heq, value?]
  next heq => simp [heq, value?]

@[always_inline, specialize query enq]
def get2 (a b : α) (ha : lt a root := by grind) (hb : lt b root := by grind) :
    ActionM hsi ci enq ({ val : β // ci hsi a val } × { val : β // ci hsi b val }) :=
  fun s hvi =>
    let va := query s a ha
    let vb := query s b hb
    let enq s a (hlt := by grind) (hq := by grind) := enq s a hlt hq
    match _ : va, _ : vb with
    | some va, some vb => ⟨s, hvi, .pure (⟨va, by grind⟩, ⟨vb, by grind⟩)⟩
    | none, some _ => ⟨enq s a, by grind, .enqueued usr rfl .init⟩
    | some _, none => ⟨enq s b, by grind, .enqueued usr rfl .init⟩
    | none, none => ⟨enq (enq s a) b, by grind, .enqueued usr rfl (by subst enq; exact .trans .init)⟩

/--
  Returns a value paired with a user state, using the default user state registered for the action.
-/
@[always_inline]
def just (val : γ) : ActionM hsi ci enq (μ × γ) :=
  return (usr, val)

@[simp, grind =]
theorem value?_just {val : γ} :
    ((just val : ActionM hsi ci enq (μ × γ)) s hvi).value? = (usr, val) := by
  simp [just]

@[always_inline]
def pair {δ : Type} (a : δ) (b : γ): ActionM hsi ci enq (δ × γ) :=
  return (a, b)

@[simp, grind =]
theorem value?_pair {δ : Type} {a : δ} {b : γ} :
    ((pair a b : ActionM hsi ci enq (δ × γ)) s hvi).value? = (a, b) := by
  simp [pair]

end ActionM
end Action

/--
  The metadata required to reason about the correctness of a visitor.
-/
structure VisitorInfo (α : Type) (β : Type := Unit) (μ : Type := Unit) where
  lt : α -> α -> Prop
  fin : FinitePartialOrder lt := by infer_instance

  stateInv : μ -> Prop := fun _ => True
  valInv : (s : μ) -> stateInv s -> α -> β -> Prop := fun _ _ _ _ => True

namespace VisitorInfo

@[simp, grind unfold]
abbrev valInv' (info : VisitorInfo α β μ) : ValInv info.stateInv α β :=
  fun {s} => info.valInv s

end VisitorInfo

variable {info : VisitorInfo α β μ}

/--
  A user provided visitor function defines the transfer function to compute the value at a given
  node. It can query earlier nodes with actions in ActionM.
-/
@[expose]
def Visitor (info : VisitorInfo α β μ) :=
  {σ : Type} -> (state : μ) -> (root : α) ->
    {hsi : info.stateInv state} ->
    {query : Query σ β info.lt root} -> {enq : Enqueue query} ->
      ActionM hsi info.valInv' enq (μ × β)

class WFVisitor (visitor : Visitor info) where
  stateInv
    {σ : Type} (state : μ) (root : α)
    {hsi : info.stateInv state}
    {query : Query σ β info.lt root} {enq : Enqueue query}
    {walk : σ} {hvi : query.respects (info.valInv state hsi) walk} :
    let motive action := ∀ hpure, info.stateInv ((action walk hvi).value?.get hpure |>.fst)
    let action := visitor state root (enq := enq)
    motive action

  valInv
    {σ : Type} (state : μ) (root : α)
    {hsi : info.stateInv state}
    {query : Query σ β info.lt root} {enq : Enqueue query}
    {walk : σ} {hvi : query.respects (info.valInv state hsi) walk} :
    let motive action :=
      ∀ hpure hsi,
        info.valInv ((action walk hvi).value?.get hpure |>.fst) hsi root ((action walk hvi).value?.get hpure |>.snd)
    let action := visitor state root (enq := enq)
    motive action

  cachePreservation
    {σ : Type} (state : μ) (root key : α) (value : β)
    {hsi : info.stateInv state}
    (valInv : info.valInv state hsi key value)
    {query : Query σ β info.lt root} {enq : Enqueue query}
    {walk : σ} {hvi : query.respects (info.valInv' hsi) walk} :
    let motive action :=
      ∀ hpure hsi,
        info.valInv ((action walk hvi).value?.get hpure |>.fst) hsi key value
    let action := visitor state root (enq := enq)
    motive action

/--
  The walker class defines a generic incremental memoizer walker that runs a `Visitor` at a given
  node.
-/
class Walker (visitor : outParam (Visitor info)) (σ : Type) where
  new : (s : μ) -> (h : info.stateInv s := by grind) -> σ
  state : σ -> μ
  visit : σ -> α -> (σ × β)

class WFWalker (visitor : outParam (Visitor info)) (σ : Type) extends Walker visitor σ where
  stateInv s : info.stateInv (state s)
  valInv s k : info.valInv' (stateInv (visit s k).fst) k (visit s k).snd

attribute [grind! .] WFWalker.stateInv WFWalker.valInv

class Cache (α β : outParam Type) (σ : Type) [DecidableEq α] where
  empty : σ
  get? : σ -> α -> Option β
  insert : σ -> α -> β -> σ
  mem : α -> σ -> Prop

  get?_mem s k : (get? s k).isSome ↔ mem k s
  get?_insert s k k' v : (get? (insert s k v) k') = if k = k' then some v else get? s k'
  mem_empty k : ¬mem k empty
  decide_mem : DecidableRel mem := by infer_instance

attribute [simp, grind! .] Cache.get?_mem
attribute [simp, grind =] Cache.get?_insert
attribute [simp, grind .] Cache.mem_empty

namespace Cache

variable [DecidableEq α] [cache : Cache α β σ] {s : σ}

instance : DecidableRel cache.mem := cache.decide_mem

@[always_inline, simp, grind]
def get (s : σ) (key : α) (h : Cache.mem key s := by grind) : β :=
  cache.get? s key |>.get (by grind)

@[simp, grind =]
theorem mem_insert {key key' : α} {val : β} :
    cache.mem key' (cache.insert s key val) ↔ key' = key ∨ cache.mem key' s := by
  grind [=_ get?_mem]

end Cache

@[always_inline, specialize α β]
instance [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [LawfulBEq α] [DecidableEq α] :
    Cache α β (Std.HashMap α β) where
  empty := .emptyWithCapacity
  get? := (·[·]?)
  insert := (·.insert · ·)
  mem := (· ∈ ·)

  get?_mem := by grind
  get?_insert := by grind
  mem_empty := by grind

@[always_inline, specialize β]
instance [Nullable β] : Cache Var { b : β // Nullable.isSome b } (VarCache β) where
  empty := .empty
  get? c var := c[var]?.filter Nullable.isSome |>.attachWith _ (by grind)
  insert := (·.insert · ·)
  mem := (· ∈ ·)

  get?_mem := by grind
  get?_insert := by grind
  mem_empty := by grind

variable [DecidableEq α]

structure DFSWalker (visitor : Visitor info) (cache : Type) [Cache α β cache] where
  cache : cache
  usr : μ
  hsi : info.stateInv usr
  hvi : ∀ k (h : Cache.mem k cache), info.valInv' hsi k (Cache.get cache k)

namespace DFSWalker
variable {visitor : Visitor info} {cache : Type} [Cache α β cache]
variable [wf : WFVisitor visitor] {walker : DFSWalker visitor cache}

/--
  A restricted view of the state for lookups.
-/
structure LookupState (cache : Type) [Cache α β cache] where
  cache : cache
  stack : Array α

namespace LookupState

@[always_inline, specialize cache α β]
abbrev query (cache : Type) [Cache α β cache] lt (root : α) : Query (LookupState cache) β lt root :=
  fun s idx _ =>
    Cache.get? s.cache idx

@[always_inline, specialize cache α β]
abbrev enqueue (cache : Type) [Cache α β cache] lt root : Enqueue (query cache lt root) :=
  fun s key _ _ =>
    ⟨{ s with stack := s.stack.push key }, by grind⟩

@[simp, grind →]
theorem cache_reach {s s'} (h : (enqueue cache lt root).reach s s') :
    s'.cache = s.cache := by
  apply Enqueue.reach.rel h <;> grind only

@[grind →]
theorem mem_stack_of_mem_stack_reach {s s'} {n : α} (h : (enqueue cache lt root).reach s s') (mem : n ∈ s'.stack) :
    n ∈ s.stack ∨ lt n root := by
  revert mem
  apply Enqueue.reach.rel h
  <;> grind

@[simp, grind .]
theorem mem_stack_reach {s s'} {n : α} (h : (enqueue cache lt root).reach s s') (mem : n ∈ s.stack) :
    n ∈ s'.stack := by
  revert mem
  apply Enqueue.reach.rel h
  <;> grind

@[simp]
theorem countP_cache_reach {s s'} (h : (enqueue cache lt root).reach s s') :
    s'.stack.countP (Cache.mem · s'.cache) = s.stack.countP (Cache.mem · s.cache) := by
  apply Enqueue.reach.rel h
  · grind [Array.countP_push]
  · grind only

@[grind .]
theorem back?_getD_lt_reach {s s'} {root' : α} (h : (enqueue cache lt root).reach s s') :
    lt (s'.stack.back?.getD root') root := by
  apply Enqueue.reach.rel h
  · grind
  · grind

end LookupState

structure State (visitor : Visitor info) (cache' : Type) (root : α) [Cache α β cache']
    extends DFSWalker visitor cache' where
  stack : Array α
  stackOrdered : ∀ x ∈ stack, info.fin.le x root

namespace State
variable {s : State visitor cache root}

def new (walker : DFSWalker visitor cache) (root : α) : State visitor cache root :=
  { walker with
    stack := #[root],
    stackOrdered := by simp
  }

abbrev Visit (info : VisitorInfo α β μ) (cache : Type) [Cache α β cache] :=
  (state : μ) -> (root : α) -> (hsi : info.stateInv state) ->
    ActionM hsi info.valInv' (LookupState.enqueue cache info.lt root) (μ × β)

def measure (s : State visitor cache root) : Nat × Nat × Nat :=
  (
    -- The number of values lt the root that are not in the cache yet decreases
    (info.fin.le_list root).countP (¬Cache.mem · s.cache),
    -- The number of values in the stack that are already in the cache decreases
    s.stack.countP (Cache.mem · s.cache),
    -- The back index of the stack decreases
    info.fin.measure (s.stack.back?.getD root)
  )

@[always_inline, specialize visitor cache visit]
def visit (s : State visitor cache root) (n : α) (visit : Visit info cache)
    (h : s.stack.back? = n := by grind) (hvisit : visit = (visitor · · (hsi := ·)) := by grind) :
    State visitor cache root :=
  let res := visit s.usr n s.hsi { s with } <| by have := s.hvi; grind

  match _ : res.action with
  | .enqueued usr _ _ =>
    { s with
      cache := res.state.cache
      stack := res.state.stack
      usr := usr
      hvi := by have := s.hvi; grind only [→ LookupState.cache_reach]
      hsi := by grind
      stackOrdered := by
        have : info.fin.le n root := by grind [s.stackOrdered]
        grind [s.stackOrdered, info.fin.trans]
    }
  | .pure (usr, val) _ =>
    { s with
      cache := Cache.insert res.state.cache n val
      stack := res.state.stack.pop
      usr := usr
      hvi k := by
        simp only [Cache.get, Cache.get?_insert]
        have := s.hvi
        have := @wf.valInv
        have := @wf.cachePreservation
        grind [ActionState.value?]
      hsi := by
        have := @wf.stateInv
        grind [ActionState.value?]
      stackOrdered := by grind [s.stackOrdered]
    }

@[simp, grind .]
theorem measure_visit {n : α} {visit h hvisit} {hmem : ¬Cache.mem n s.cache} :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (s.visit n visit h hvisit).measure s.measure := by
  have : info.fin.le n root := by grind [s.stackOrdered]
  fun_cases visit
  next hreach _ =>
    apply Prod.Lex.right'
    · grind
    · apply Prod.Lex.right'
      · simp [LookupState.countP_cache_reach hreach]
      · apply info.fin.measure_lt
        grind
  next heq _ =>
    apply Prod.Lex.left
    simp only [heq, Cache.mem_insert, not_or, Bool.decide_and,
      FinitePartialOrder.le_list, List.countP_eq_length_filter, ← List.filter_filter,
      List.length_filter_lt_length_iff_exists]
    grind

@[simp, grind .]
theorem mem_cache_visit_of_mem_cache {n x : α} {visit h hvisit} (mem : Cache.mem x s.cache) :
    Cache.mem x (s.visit n visit h hvisit).cache := by
  fun_cases visit <;> grind

@[simp, grind .]
theorem mem_cache_visit_of_mem_stack {n x : α} {visit h hvisit} (mem : x ∈ s.stack) :
    x ∈ (s.visit n visit h hvisit).stack ∨ Cache.mem x (s.visit n visit h hvisit).cache := by
  fun_cases visit
  · grind
  · grind [Array.mem_iff_getElem]

@[always_inline, specialize visitor cache visit]
def step (s : State visitor cache root) (n : α) (visit : Visit info cache)
    (h : s.stack.back? = n := by grind) (hvisit : visit = (visitor · · (hsi := ·)) := by grind) :
    State visitor cache root :=
  match _ : Cache.get? s.cache n with
  | some _ => { s with stack := s.stack.pop, stackOrdered := by grind [s.stackOrdered] }
  | none => s.visit n visit

@[simp, grind .]
theorem measure_step {n : α} {visit h hvisit} :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (s.step n visit h hvisit).measure s.measure := by
  fun_cases step
  · apply Prod.Lex.right'
    · grind
    · apply Prod.Lex.left
      simp
      apply Nat.sub_lt
      · grind [Array.countP_pos_iff]
      · grind
  · grind

@[simp, grind .]
theorem mem_cache_step_of_mem_cache {n x : α} {visit h hvisit} (mem : Cache.mem x s.cache) :
    Cache.mem x (s.step n visit h hvisit).cache := by
  fun_cases step <;> grind

@[simp, grind .]
theorem mem_cache_step_of_mem_stack {n x : α} {visit h hvisit} (mem : x ∈ s.stack) :
    x ∈ (s.step n visit h hvisit).stack ∨ Cache.mem x (s.step n visit h hvisit).cache := by
  fun_cases step
  · grind [Array.mem_iff_getElem]
  · grind

@[always_inline, specialize visitor cache]
private def walk.rebuildDFSWalker (walker : DFSWalker visitor cache)
    (cache' : cache) (usr : μ)
    (hcache : walker.cache = cache' := by grind)
    (husr : walker.usr = usr := by grind) :
    DFSWalker visitor cache := by
  apply DFSWalker.mk cache' usr
  <;> simp only [←hcache, ←husr]
  · refine walker.hvi
  · refine walker.hsi

omit wf in
@[simp, grind =]
private theorem walk.rebuildDFSWalker_eq (walker : DFSWalker visitor cache) cache' usr hcache husr :
    rebuildDFSWalker walker cache' usr hcache husr = walker := by
  simp [rebuildDFSWalker, ←hcache, ←husr]

open walk in
@[always_inline, specialize visitor cache]
private def walk.rebuildState (s : State visitor cache root)
    (cache' : cache) (usr : μ) (stack : Array α)
    (hcache : s.cache = cache' := by grind)
    (husr : s.usr = usr := by grind)
    (hstack : s.stack = stack := by grind) :
    State visitor cache root := by
  let walker := rebuildDFSWalker s.toDFSWalker cache' usr
  apply State.mk walker stack
  <;> simp only [←hstack]
  · refine s.stackOrdered

omit wf in
@[simp, grind =]
private theorem walk.rebuildState_eq (s : State visitor cache root)
    cache' usr stack hcache husr hstack :
    rebuildState s cache' usr stack hcache husr hstack = s := by
  simp [rebuildState, ←hcache, ←husr, ←hstack]

@[always_inline, specialize visitor cache]
private def walk.walkSpec (s : State visitor cache root) (visit : Visit info cache)
    (hvisit : visit = (visitor · · (hsi := ·)) := by grind) :
    State visitor cache root :=
  go s s.cache s.usr s.stack
where
  @[specialize visitor cache visit]
  go (s : State visitor cache root)
      (cache' : cache) (usr : μ) (stack : Array α)
      (hcache : s.cache = cache' := by grind)
      (husr : s.usr = usr := by grind)
      (hstack : s.stack = stack := by grind) :
      State visitor cache root :=
    let s' := rebuildState s cache' usr stack
    match _ : s'.stack.back? with
    | none => s'
    | some n =>
      let s' := s'.step n visit
      go s' s'.cache s'.usr s'.stack
  termination_by s.measure

open walk in
/-
  We provide a custom implementation of the actual walker loop that doesn't box its arguments,
  which when combined with liberal inlining allows the whole loop to be inlined into one loop
  without boxing.
-/
@[always_inline, specialize visitor cache]
private def walk (s : State visitor cache root) : State visitor cache root :=
  walk.walkSpec s (visitor · · (hsi := ·))

def walkSlow (s : State visitor cache root) : State visitor cache root :=
  match _ : s.stack.back? with
  | none => s
  | some n => walkSlow (s.step n (visitor · · (hsi := ·)))
termination_by s.measure

@[simp, grind =]
private theorem walk_eq_walkSlow :
    s.walk = s.walkSlow := by
  unfold walk walk.walkSpec
  fun_induction walkSlow
  <;> unfold walk.walkSpec.go
  <;> grind

@[simp, grind .]
theorem mem_cache_walkSlow_of_mem_cache {n : α} (mem : Cache.mem n s.cache) :
    Cache.mem n s.walkSlow.cache := by
  fun_induction walkSlow <;> grind

@[simp, grind .]
theorem mem_cache_walkSlow_of_mem_stack {n : α} (mem : n ∈ s.stack) :
    Cache.mem n s.walkSlow.cache := by
  fun_induction walkSlow <;> grind

end State

@[always_inline, specialize visitor cache]
def visit (s : DFSWalker visitor cache) (root : α) : DFSWalker visitor cache × β :=
  match Cache.get? s.cache root with
  | some v => (s, v)
  | none =>
    let s := State.new s root |>.walk
    let walker := s.toDFSWalker
    ⟨walker, Cache.get? walker.cache root |>.get <| by grind [State.new]⟩

@[always_inline, specialize visitor cache]
instance instWalker : WFWalker visitor (DFSWalker visitor cache) where
  new usr hsi := { cache := Cache.empty, usr, hsi, hvi := by grind }
  state := (·.usr)
  visit := visit

  stateInv s := s.hsi
  valInv s k := by have := @DFSWalker.hvi; grind [visit]

end DFSWalker

set_option warn.classDefReducibility false in
@[always_inline, specialize visitor cache]
def dfsWalker (visitor : Visitor info) [WFVisitor visitor] (cache : Type) [Cache α β cache] :
    WFWalker visitor (DFSWalker visitor cache) :=
  DFSWalker.instWalker

set_option warn.classDefReducibility false in
@[always_inline, specialize visitor]
def dfsHashWalker [Hashable α] (visitor : Visitor info) [WFVisitor visitor] :
    WFWalker visitor (DFSWalker visitor (Std.HashMap α β)) :=
  DFSWalker.instWalker

end Valaig.Data.Memo
