module

public import Std.Data.HashMap.Basic
public import Std.Data.HashMap.Iterator
import Std.Data.HashMap.Lemmas

namespace Valaig.Utils

public section

/--
`Pool α` is a memory pool data structure that allows storing, modifying, retrieving and freeing
values referenced by unique `Nat` indices.

It is currently backed by `Std.HashMap`, but this may change in the future.
-/
structure Pool (α : Type) where
  idx : Nat
  values : Std.HashMap Nat α
  ltIdx {idx' : Nat} : values.contains idx' → idx' < idx

namespace Pool
variable {α : Type} {pool : Pool α} {idx idx' : Nat} {v : α}

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

@[inline, local simp, local grind]
def size (pool : Pool α) : Nat :=
  pool.values.size

/--
Creates an empty pool with memory allocated for `capacity` elements.
-/
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
    (pool.add v).fst[(pool.add v).snd]'(by grind) = v := by
  grind [add]

@[simp]
theorem getElem_add (h : idx ∈ pool) :
    (pool.add v).fst[idx]'(by grind) = pool[idx] := by
  grind [add]

grind_pattern getElem_add => (pool.add v).fst[idx]'(by grind) where
  idx =/= (pool.add v).snd

@[simp, grind =]
theorem size_add :
    (pool.add v).fst.size = pool.size + 1 := by
  have : (pool.add v).snd ∉ pool := by grind
  grind [add]

/--
Removes an element from the pool by index. If there is no element allocated with that index, the
pool is returned unchanged.
-/
@[inline]
def remove (pool : Pool α) (idx : Nat) : Pool α :=
  { pool with
    values := pool.values.erase idx
    ltIdx := by have := @pool.ltIdx; grind
  }

@[simp, grind =]
theorem mem_remove_iff :
    idx ∈ (pool.remove idx') ↔
      idx ≠ idx' ∧ idx ∈ pool := by
  grind [remove]

@[simp, grind =]
theorem getElem_remove (h : idx ∈ pool.remove idx') :
    (pool.remove idx')[idx] = pool[idx]'(by grind) := by
  grind [remove]

@[simp, grind =]
theorem size_remove :
    (pool.remove idx).size =
    if idx ∈ pool then
      pool.size - 1
    else
      pool.size := by
  grind [remove]

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
    (pool.modify idx f)[idx]'(by grind) = f pool[idx] := by
  grind [modify]

@[simp]
theorem getElem_modify {f : α -> α} (h : idx ∈ pool) :
    (pool.modify idx' f)[idx]'(by grind) =
    if idx = idx' then
      f pool[idx]
    else
      pool[idx] := by
  grind [modify]

grind_pattern getElem_modify => (pool.modify idx' f)[idx]'(by grind) where
  idx =/= idx'

@[simp, grind =]
theorem size_modify {f : α -> α} :
    (pool.modify idx f).size = pool.size := by
  grind [modify]

/--
Replaces the element at a given index in the pool. See also `set?`.
-/
@[inline]
def set (pool : Pool α) (idx : Nat) (v : α) (h : idx ∈ pool := by get_elem_tactic) : Pool α :=
  { pool with
    values := pool.values.insert idx v
    ltIdx := by have := @pool.ltIdx; grind [contains]
  }

@[simp, grind =]
theorem mem_set_iff (h : idx' ∈ pool) :
    idx ∈ (pool.set idx' v h) ↔ idx ∈ pool := by
  grind [set]

@[simp, grind =]
theorem getElem_set_self (h : idx ∈ pool) :
    (pool.set idx v h)[idx]'(by grind) = v := by
  grind [set]

@[simp]
theorem getElem_set (h : idx ∈ pool) (h' : idx' ∈ pool) :
    (pool.set idx' v h')[idx]'(by grind) =
    if idx = idx' then
      v
    else
      pool[idx] := by
  grind [set]

grind_pattern getElem_set => (pool.set idx' v h')[idx]'(by grind) where
  idx =/= idx'

@[simp, grind =]
theorem size_set (h : idx ∈ pool ) :
    (pool.set idx v h).size = pool.size := by
  grind [set]

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
    (pool.set? idx v)[idx]'(by grind) = v := by
  grind [set?]

@[simp]
theorem getElem_set? (h : idx ∈ pool) :
    (pool.set? idx' v)[idx]'(by grind) =
    if idx = idx' then
      v
    else
      pool[idx] := by
  grind [set?]

grind_pattern getElem_set? => (pool.set? idx' v)[idx]'(by grind) where
  idx =/= idx'

@[simp, grind =]
theorem size_set? :
    (pool.set? idx v).size = pool.size := by
  grind [set?]
