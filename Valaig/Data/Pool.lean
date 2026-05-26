module

public import Std.Data.HashMap.Basic
public import Std.Data.HashMap.Iterator
public import Valaig.Prelude
import Std.Data.HashMap.IteratorLemmas
import Std.Data.HashMap.Lemmas

public section
namespace Valaig.Data

/--
  `Pool α` is a memory pool data structure that allows storing, modifying, retrieving and freeing
  values referenced by unique `Nat` indices.

  It is currently backed by `Std.HashMap`, but this may change in the future.
-/
structure Pool (α : Type) where
  idx : Nat
  values : Std.HashMap Nat α
  ltIdx {idx' : Nat} : values.contains idx' → idx' < idx
deriving Repr

namespace Pool
variable {α : Type} {pool : Pool α} {idx idx' : Nat} {v : α}

instance : Inhabited (Pool α) where
  default := { idx := 0, values := .emptyWithCapacity, ltIdx := by grind }

@[inline]
def contains (pool : Pool α) (idx : Nat) : Bool :=
  pool.values.contains idx

instance instMembership : Membership Nat (Pool α) where
  mem pool idx := idx ∈ pool.values

@[inline]
instance {pool : Pool α} {idx : Nat} : Decidable (idx ∈ pool) := by
  simp only [Membership.mem]
  infer_instance

@[local simp, local grind =]
private theorem mem_eq :
    (idx ∈ pool) = (idx ∈ pool.values) := by
  rfl

@[simp, grind =]
theorem contains_eq_mem :
    pool.contains idx = decide (idx ∈ pool) := by
  grind [contains]

@[inline]
instance : GetElem (Pool α) Nat α (fun pool idx => idx ∈ pool) where
  getElem pool idx h := pool.values[idx]

@[local simp, local grind =]
private theorem getElem_eq (h : idx ∈ pool) :
    pool[idx] = pool.values[idx] := by
  rfl

@[inline]
instance : GetElem? (Pool α) Nat α (fun pool idx => idx ∈ pool) where
  getElem? pool idx := pool.values[idx]?

@[local simp, local grind =]
private theorem getElem?_eq :
    pool[idx]? = pool.values[idx]? := by
  rfl

instance : LawfulGetElem (Pool α) Nat α (fun pool idx => idx ∈ pool) where
  getElem?_def := by grind

/--
Returns the number of elements currently in the pool.
-/
@[inline, local simp, local grind]
def size (pool : Pool α) : Nat :=
  pool.values.size

/--
Returns a new index that is not currently valid within the pool. This can be used with `insert`
to manually construct a new element in the pool.
-/
def nextIdx (pool : Pool α) : Nat :=
  pool.idx

@[simp, grind .]
theorem nextIdx_not_in :
    pool.nextIdx ∉ pool := by
  have := @pool.ltIdx
  grind [nextIdx]

/--
Creates an empty pool with memory allocated for `capacity` elements.
-/
@[inline]
def emptyWithCapacity (capacity : Nat := 8) : Pool α :=
  {
    idx := 0
    values := .emptyWithCapacity capacity
    ltIdx := by simp
  }

@[simp, grind .]
theorem not_mem_emptyWithCapacity {cap : Nat} :
    ¬(idx ∈ (emptyWithCapacity cap : Pool α)) := by
  grind [emptyWithCapacity]

@[simp, grind .]
theorem size_emptyWithCapacity {cap : Nat} :
    (emptyWithCapacity cap : Pool α).size = 0 := by
  grind [emptyWithCapacity]

/--
Creates an empty pool with no memory allocated for elements.
-/
@[inline]
def empty : Pool α :=
  .emptyWithCapacity 0

@[simp, grind .]
theorem not_mem_empty :
    ¬(idx ∈ (empty : Pool α)) := by
  grind [empty]

@[simp, grind =]
theorem size_empty :
    (empty : Pool α).size = 0 := by
  grind [empty]

/--
Adds a new element to the pool, returning the updated pool and a unique index for the new element.
-/
@[inline]
def add (pool : Pool α) (v : α) : Pool α × Nat :=
  ({
    idx := pool.idx + 1
    values := pool.values.insert pool.idx v
    ltIdx := by have := @pool.ltIdx; grind
  }, pool.idx)

@[simp, grind =]
theorem mem_add_iff :
    idx ∈ (pool.add v).fst ↔
      idx = (pool.add v).snd ∨ idx ∈ pool := by
  grind [add]

@[simp, grind .]
theorem not_mem_add :
    (pool.add v).snd ∉ pool := by
  have := @pool.ltIdx
  grind [add]

@[simp, grind =]
theorem getElem_add_self :
    (pool.add v).fst[(pool.add v).snd] = v := by
  grind [add]

@[simp]
theorem getElem_add (h : idx ∈ pool) :
    (pool.add v).fst[idx] = pool[idx] := by
  grind [add]

grind_pattern getElem_add => (pool.add v).fst[idx] where
  idx =/= (pool.add v).snd

@[simp, grind =]
theorem size_add :
    (pool.add v).fst.size = pool.size + 1 := by
  have : (pool.add v).snd ∉ pool := by grind
  grind [add]

/--
Adds a new `Inhabited.default` element to the pool, returning the updated pool and a unique index
for the new element.
-/
@[inline]
def addD [Inhabited α] (pool : Pool α) : Pool α × Nat :=
  pool.add Inhabited.default

@[simp, grind =]
theorem addD_eq [Inhabited α] :
    pool.addD = pool.add Inhabited.default := by
  rfl

/--
Removes an element from the pool by index. If there is no element allocated with that index, the
pool is returned unchanged.
-/
@[inline]
def erase (pool : Pool α) (idx : Nat) : Pool α :=
  { pool with
    values := pool.values.erase idx
    ltIdx := by have := @pool.ltIdx; grind
  }

@[simp, grind =]
theorem mem_erase_iff :
    idx ∈ (pool.erase idx') ↔
      idx ≠ idx' ∧ idx ∈ pool := by
  grind [erase]

@[simp, grind =]
theorem getElem_erase (h : idx ∈ pool.erase idx') :
    (pool.erase idx')[idx] = pool[idx] := by
  grind [erase]

@[simp, grind =]
theorem size_erase :
    (pool.erase idx).size =
    if idx ∈ pool then
      pool.size - 1
    else
      pool.size := by
  grind [erase]

/--
Inserts a new element at an index in the pool, growing the pool if needed. If the pool already
contains an element at this index, it is overwritten.
-/
@[inline]
def insert (pool : Pool α) (idx : Nat) (v : α) : Pool α :=
  { idx := max pool.idx (idx + 1)
    values := pool.values.insert idx v
    ltIdx := by have := @pool.ltIdx; grind
  }

@[simp, grind =]
theorem mem_insert_iff :
    idx ∈ pool.insert idx' v ↔
      idx ∈ pool ∨ idx = idx' := by
  grind [insert]

@[simp, grind =]
theorem getElem_insert_self :
    (pool.insert idx v)[idx] = v := by
  grind [insert]

@[simp]
theorem getElem_insert (h : idx ∈ pool.insert idx' v) :
    (pool.insert idx' v)[idx] =
    if h : idx = idx' then
      v
    else
      pool[idx] := by
  grind [insert]

grind_pattern getElem_insert => (pool.insert idx' v)[idx] where
  idx =/= idx'

@[simp, grind =]
theorem size_insert :
    (pool.insert idx v).size =
    if idx ∈ pool then
      pool.size
    else
      pool.size + 1 := by
  grind [insert]

/--
Replaces the element at a given index in the pool. See also `set?`.
-/
@[inline]
def set (pool : Pool α) (idx : Nat) (v : α) (h : idx ∈ pool := by get_elem_tactic) : Pool α :=
  { pool with
    values := pool.values.insert idx v
    ltIdx := by have := @pool.ltIdx; grind
  }

@[simp, grind =]
theorem mem_set_iff (h : idx' ∈ pool) :
    idx ∈ (pool.set idx' v h) ↔ idx ∈ pool := by
  grind [set]

@[simp, grind =]
theorem getElem_set_self (h : idx ∈ pool) :
    (pool.set idx v h)[idx] = v := by
  grind [set]

@[simp]
theorem getElem_set (h : idx ∈ pool) (h' : idx' ∈ pool) :
    (pool.set idx' v h')[idx] =
    if idx = idx' then
      v
    else
      pool[idx] := by
  grind [set]

grind_pattern getElem_set => (pool.set idx' v h')[idx] where
  idx =/= idx'

@[simp, grind =]
theorem size_set (h : idx ∈ pool ) :
    (pool.set idx v h).size = pool.size := by
  grind [set]

/--
Replaces an element at the given index with the result of applying `f` to it. If there is no element
allocated with that index, the pool is returned unchanged.

The reference count to the element is decremented before applying `f`, allowing in-place updates.
-/
@[inline]
def modify (pool : Pool α) (idx : Nat) (f : α -> α) : Pool α :=
  { pool with
    values := pool.values.modify idx f
    ltIdx := by have := @pool.ltIdx; grind
  }

@[simp, grind =]
theorem mem_modify_iff {f : α -> α} :
    idx ∈ (pool.modify idx' f) ↔ idx ∈ pool := by
  grind [modify]

@[simp, grind =]
theorem getElem_modify_self {f : α -> α} (h : idx ∈ pool) :
    (pool.modify idx f)[idx] = f pool[idx] := by
  grind [modify]

@[simp]
theorem getElem_modify {f : α -> α} (h : idx ∈ pool) :
    (pool.modify idx' f)[idx] =
    if idx = idx' then
      f pool[idx]
    else
      pool[idx] := by
  grind [modify]

grind_pattern getElem_modify => (pool.modify idx' f)[idx] where
  idx =/= idx'

@[simp, grind =]
theorem size_modify {f : α -> α} :
    (pool.modify idx f).size = pool.size := by
  grind [modify]

/--
Replaces an element at the given index with the result of applying `f` to it, providing a proof that
the element being modified matches the element visible to `GetElem?`.

The reference count to the element is decremented before applying `f` by replacing the element with
`Inhabited.default`, allowing in-place updates.
-/
@[inline]
def modifyMem [Inhabited α] (pool : Pool α) (idx : Nat) (f : { elem : α // pool[idx]? = some elem } -> α)
     (h : idx ∈ pool := by get_elem_tactic) : Pool α :=
  let val := pool[idx]
  let pool := pool.set idx Inhabited.default
  pool.modify idx (fun _ => f ⟨val, by grind⟩)

@[simp, grind =]
theorem mem_modifyMem_iff [Inhabited α] {f : { elem : α // pool[idx']? = some elem } -> α} (h : idx' ∈ pool) :
    idx ∈ pool.modifyMem idx' f h ↔ idx ∈ pool := by
  grind [modifyMem]

@[simp, grind =]
theorem getElem_modifyMem_self [Inhabited α] {f : { elem : α // pool[idx]? = some elem } -> α} (h : idx ∈ pool) :
    (pool.modifyMem idx f h)[idx] = f ⟨pool[idx], by grind⟩ := by
  grind [modifyMem]

@[simp]
theorem getElem_modifyMem [Inhabited α] {f : { elem : α // pool[idx']? = some elem } -> α} (h : idx ∈ pool) (h' : idx' ∈ pool) :
    (pool.modifyMem idx' f h')[idx] =
    if h : idx = idx' then
      f ⟨pool[idx], by grind⟩
    else
      pool[idx] := by
  grind [modifyMem]

grind_pattern getElem_modifyMem => (pool.modifyMem idx' f h')[idx] where
  idx =/= idx'

@[simp, grind =]
theorem size_modifyMem [Inhabited α] {f : { elem : α // pool[idx]? = some elem } -> α} (h : idx ∈ pool) :
    (pool.modifyMem idx f h).size = pool.size := by
  grind [modifyMem]

/--
Replaces the element at a given index in the pool. If there is no element allocated with that index,
the pool is returned unchanged.
-/
@[inline]
def set? (pool : Pool α) (idx : Nat) (v : α) : Pool α :=
  pool.modify idx (fun _ => v)

@[simp, grind =]
theorem mem_set?_iff :
    idx ∈ (pool.set? idx' v) ↔ idx ∈ pool := by
  grind [set?]

@[simp, grind =]
theorem getElem_set?_self (h : idx ∈ pool) :
    (pool.set? idx v)[idx] = v := by
  grind [set?]

@[simp]
theorem getElem_set? (h : idx ∈ pool) :
    (pool.set? idx' v)[idx] =
    if idx = idx' then
      v
    else
      pool[idx] := by
  grind [set?]

grind_pattern getElem_set? => (pool.set? idx' v)[idx] where
  idx =/= idx'

@[simp, grind =]
theorem size_set? :
    (pool.set? idx v).size = pool.size := by
  grind [set?]

@[simp←]
theorem size_zero_iff_forall_not_in :
    pool.size = 0 ↔ ∀ (idx : Nat), idx ∉ pool := by
  rw [show pool.size = 0 ↔ pool.values.isEmpty by grind [Std.HashMap.isEmpty_eq_size_eq_zero]]
  simp [Std.HashMap.isEmpty_iff_forall_contains]

grind_pattern size_zero_iff_forall_not_in => (_ : Nat) ∈ pool, pool.size

@[expose, reducible]
def IterState (pool : Pool α) : Type :=
  let getType {α β} (_ : @Std.Iter α β) := α
  getType pool.values.keysIter

/--
Returns an iterator over the valid indices in the pool.
-/
@[inline]
def iter (pool : Pool α) :=
  pool.values.keysIter

@[simp, grind =]
theorem mem_iter_toList_iff_mem :
    idx ∈ pool.iter.toList ↔ idx ∈ pool := by
  simp [iter]

@[simp, grind =]
theorem length_iter_eq_size :
    pool.iter.length = pool.size := by
  simp [iter, ←Std.Iter.length_toList_eq_length]

@[simp, grind =]
theorem length_toList_iter :
    pool.iter.toList.length = pool.size := by
  simp

@[simp, grind .]
theorem nodup_toList_iter :
    pool.iter.toList.Nodup := by
  simp [iter, Std.HashMap.nodup_keys]

theorem distinct_toList_iter {idx idx' : Nat} (h : idx < pool.size) (h' : idx' < pool.size)
    (diff : idx ≠ idx') :
      pool.iter.toList[idx] ≠ pool.iter.toList[idx'] := by
  grind [@nodup_toList_iter _ pool, List.pairwise_iff_getElem]

grind_pattern distinct_toList_iter => pool.iter.toList[idx]'_, pool.iter.toList[idx']'_ where
  idx =/= idx'
