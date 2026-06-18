module

public import Valaig.ForLean.Prelude
public import Std.Data.HashSet
import Std.Data.Iterators.Producers.Range
import Std.Data.Iterators.Lemmas.Producers.Range
public import Valaig.ForLean.Array

public section
namespace Valaig.Data

/--
  `Pool α` is a memory pool data structure that allows storing, modifying, retrieving and freeing
  values referenced by unique `Nat` indices.
-/
structure Pool (α : Type) where
  values : Array α
  frees : Std.HashSet Nat

  freesValid : ∀ n ∈ frees, n < values.size

namespace Pool
variable {α : Type} {pool : Pool α} {idx idx' : Nat} {v : α}
attribute [local simp, local grind →] Pool.freesValid
attribute [local grind =] Std.HashSet.toList_iter
attribute [local grind =_] Std.HashSet.mem_toList Std.Iter.getElem?_toList_eq_atIdxSlow?

private theorem frees_perm :
    pool.frees.iter.toList.Perm (List.range pool.values.size |>.filter (· ∈ pool.frees)) := by
  simp only [Std.HashSet.toList_iter, List.perm_iff_count]
  grind [List.Nodup.count, Std.HashSet.distinct_toList, List.count_filter]

@[local simp, local grind =]
private theorem rco_eq_range {n : Nat} :
    (0...n).toList = List.range n := by
  apply List.ext_get <;> simp

@[local simp, local grind .]
private theorem size_frees_le_size_values :
    pool.frees.size ≤ pool.values.size := by
  rw [show pool.frees.size = pool.frees.iter.toList.length by simp, List.Perm.length_eq frees_perm]
  grind

/--
  The greatest number of elements that have been constructed up this point.
  As indices are reused with a free list, indices from the free list are
  guaranteed to be less than this.
-/
@[inline, local simp, local grind]
def capacity (pool : Pool α) :=
  pool.values.size

@[inline]
def contains (pool : Pool α) (idx : Nat) : Bool :=
  idx < pool.capacity ∧ idx ∉ pool.frees

instance instMembership : Membership Nat (Pool α) where
  mem pool idx := pool.contains idx

@[inline]
instance {pool : Pool α} {idx : Nat} : Decidable (idx ∈ pool) := by
  simp +instances only [instMembership]
  infer_instance

@[local simp, local grind =]
private theorem mem_iff :
    idx ∈ pool ↔ idx < pool.capacity ∧ idx ∉ pool.frees := by
  simp +instances [instMembership, contains]

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

/--
  Return the number of elements currently in the pool.
-/
@[inline, local simp, local grind]
def size (pool : Pool α) : Nat :=
  pool.capacity - pool.frees.size

/--
  Return a new index that is not currently valid within the pool. This can be used with `insert`
  to manually construct a new element in the pool.
-/
@[inline]
def nextIdx (pool : Pool α) : Nat :=
  pool.frees.iter.atIdxSlow? 0 |>.getD pool.capacity

@[simp, grind .]
theorem nextIdx_not_in :
    pool.nextIdx ∉ pool := by
  grind [nextIdx]

/--
  Create an empty pool with no memory allocated for elements.
-/
@[inline]
def empty : Pool α :=
  { values := #[], frees := .emptyWithCapacity, freesValid := by grind }

@[simp, grind .]
theorem not_mem_empty :
    ¬(idx ∈ (empty : Pool α)) := by
  grind [empty]

@[simp, grind =]
theorem size_empty :
    (empty : Pool α).size = 0 := by
  grind [empty]

@[simp, grind =]
theorem capacity_empty :
    (empty : Pool α).capacity = 0 := by
  grind [empty]

@[inline]
instance : Inhabited (Pool α) where
  default := empty

section erase
variable [Inhabited α]

/--
  Remove an element from the pool by index.
-/
@[inline]
def erase (pool : Pool α) (idx : Nat) (mem : idx ∈ pool := by grind) : Pool α :=
  {
    values := pool.values.set idx Inhabited.default
    frees := pool.frees.insert idx
    freesValid := by grind
  }

variable {mem : idx ∈ pool}
attribute [local simp, local grind] erase

@[simp, grind =]
theorem mem_erase_iff {idx' : Nat} :
    idx' ∈ (pool.erase idx mem) ↔
      idx' ≠ idx ∧ idx' ∈ pool := by
  grind

@[simp, grind =]
theorem getElem_erase (h : idx' ∈ pool.erase idx mem) :
    (pool.erase idx mem)[idx']'h = pool[idx'] := by
  grind

@[simp, grind =]
theorem size_erase :
    (pool.erase idx mem).size = pool.size - 1 := by
  grind

@[simp, grind =]
theorem capacity_erase :
    (pool.erase idx mem).capacity = pool.capacity := by
  grind

end erase

/--
  Insert an element with index `nextIdx`.
-/
@[inline]
def push (pool : Pool α) (v : α) : Pool α :=
  if hempty : pool.frees.isEmpty then
    {
      values := pool.values.push v
      frees := pool.frees
      freesValid := by grind
    }
  else
    match h : pool.frees.iter.atIdxSlow? 0 with
    | some n => {
        values := pool.values.set n v <| by apply pool.freesValid; grind
        frees := pool.frees.erase n
        freesValid := by grind
      }
    | none => by grind [Std.HashSet.isEmpty_eq_size_eq_zero]

section push
attribute [local simp, local grind] push nextIdx
attribute [local grind =] Std.HashSet.isEmpty_eq_size_eq_zero

@[simp, grind =]
theorem mem_push_iff :
    idx ∈ pool.push v ↔
      idx ∈ pool ∨ idx = pool.nextIdx := by
  grind

@[simp, grind =]
theorem getElem_push (mem : idx ∈ pool.push v) :
    (pool.push v)[idx]'mem =
    if h : idx = pool.nextIdx then
      v
    else
      pool[idx] := by
  grind

@[simp, grind =]
theorem size_push :
    (pool.push v).size = pool.size + 1 := by
  grind [size_frees_le_size_values]

@[simp]
theorem capacity_push :
    (pool.push v).capacity ≤ pool.capacity + 1 := by
  grind

grind_pattern capacity_push => (pool.push v).capacity

end push

set_option linter.unusedVariables false in
/--
  Replace an element at the given index with the result of applying `f` to it.
  The reference count to the element is decremented before applying `f`, allowing in-place updates.
-/
@[inline]
def modify (pool : Pool α) (idx : Nat) (f : α -> α) (mem : idx ∈ pool := by grind) : Pool α :=
  { pool with
    values := pool.values.modify idx f
    freesValid := by grind
  }

section modify
variable {f : α -> α} {mem : idx ∈ pool}
attribute [local simp, local grind] modify

@[simp, grind =]
theorem mem_modify_iff :
    idx' ∈ (pool.modify idx f mem) ↔ idx' ∈ pool := by
  grind

@[simp, grind =]
theorem getElem_modify {mem' : idx' ∈ pool.modify idx f mem}:
    (pool.modify idx f mem)[idx']'mem' =
    if idx' = idx then
      f pool[idx']
    else
      pool[idx'] := by
  grind

@[simp, grind =]
theorem size_modify :
    (pool.modify idx f).size = pool.size := by
  grind

@[simp, grind =]
theorem capacity_modify :
    (pool.modify idx f).capacity = pool.capacity := by
  grind

end modify

set_option linter.unusedVariables false in
/--
  Move a value from an index into the pool to another index that is currently free or the same index,
  resizing if required.
-/
def move [Inhabited α] (pool : Pool α) (old new : Nat) (mem : old ∈ pool := by grind) (notmem : new ∉ pool ∨ new = old := by grind) : Pool α :=
  if _ : new = old then
    pool
  else
    -- Erase new from the free-list if needed and expand the array to have space
    let pool : { p : Pool α // old < p.capacity ∧ new < p.capacity } :=
      if _ : new < pool.capacity then
        ⟨{ pool with
          frees := pool.frees.erase new
          freesValid := by grind
        }, by grind⟩
      else
        let ⟨pool, _⟩ := resize pool
        ⟨{ pool with
          values := pool.values.push Inhabited.default
          freesValid := by grind
        }, by grind⟩

    {
      values := pool.val.values.swap old new
      frees := pool.val.frees.insert old
      freesValid := by grind
    }
where
  -- Expand the array with freed default elements up to a size of new
  resize (pool : Pool α) (size : pool.capacity ≤ new := by grind) : { p : Pool α // p.capacity = new } :=
    if _ : pool.capacity = new then
      ⟨pool, by grind⟩
    else
      resize {
        values := pool.values.push Inhabited.default
        frees := pool.frees.insert pool.capacity
        freesValid := by grind
      }
  termination_by new + 1 - pool.capacity
  decreasing_by grind

section move
variable [Inhabited α] {old new : Nat} {mem : old ∈ pool} (notmem : new ∉ pool ∨ new = old) (size : pool.capacity ≤ new)
attribute [local simp, local grind] move

@[simp, grind =]
private theorem move.size_resize :
    (move.resize new pool size).val.size = pool.size := by
  fun_induction move.resize <;> grind

@[simp, grind =]
private theorem move.size_values_resize :
    (move.resize new pool size).val.values.size = new := by
  grind

@[simp, grind =]
private theorem move.size_frees_resize :
    (move.resize new pool size).val.frees.size = pool.frees.size + (pool.capacity...new).size := by
  fun_induction move.resize <;> grind [Nat.size_rco]

@[simp, grind =]
private theorem move.mem_resize :
    idx ∈ (move.resize new pool size).val ↔ idx ∈ pool  := by
  fun_induction move.resize <;> grind

@[simp, grind =]
private theorem move.mem_frees_resize :
    idx ∈ (move.resize new pool size).val.frees ↔
    idx ∈ pool.frees ∨
    idx ∈ (pool.capacity...new) := by
  fun_induction move.resize <;> grind [Std.Rco.mem_iff]

@[simp, grind =]
private theorem move.getElem_values_resize (mem : idx < (move.resize new pool size).val.values.size) mem' :
    (move.resize new pool size).val.values[idx]'mem = pool[idx]'mem' := by
  fun_induction move.resize <;> grind

@[simp, grind =]
theorem size_move :
    (pool.move old new mem notmem).size = pool.size := by
  simp only [move]
  split
  · grind
  · split
    · have : pool.frees.isEmpty = false := by grind [Std.HashSet.isEmpty_iff_forall_not_mem]
      grind [Std.HashSet.isEmpty_eq_size_eq_zero]
    · grind [Std.Rco.mem_iff, Nat.size_rco]

@[simp, grind =]
theorem capacity_move :
    (pool.move old new mem notmem).capacity = max pool.capacity (new + 1) := by
  grind

@[simp, grind =]
theorem mem_move :
    idx ∈ pool.move old new mem notmem ↔
    (idx ≠ old ∧ idx ∈ pool) ∨ idx = new := by
  grind [Std.Rco.mem_iff]

@[simp, grind =]
theorem getElem_move (mem' : idx ∈ pool.move old new mem notmem) :
    (pool.move old new mem notmem)[idx]'mem' =
    if _ : idx = new then
      pool[old]'mem
    else
      have h : idx ∈ pool := by grind
      pool[idx]'h := by
  grind

end move

/--
  Return an iterator over the valid indices in the pool.
-/
@[inline]
def iter (pool : Pool α) :=
  (0...pool.values.size).iter.filter (· ∉ pool.frees)

@[simp, grind =]
theorem mem_iter_toList_iff_mem :
    idx ∈ pool.iter.toList ↔ idx ∈ pool := by
  simp [iter]

@[simp, grind =]
theorem length_iter_eq_size :
    pool.iter.length = pool.size := by
  simp only [iter, ← Std.Iter.length_toList_eq_length, Std.Iter.toList_filter, ← List.countP_eq_length_filter]
  have {α : Type} {l : List α} f : l.countP f = l.length - l.countP (!f ·) := by grind [List.length_eq_countP_add_countP]
  rw [this, Std.Rco.toList_iter, Std.Rco.length_toList]
  congr 1
  rw [show pool.frees.size = pool.frees.iter.toList.length by simp, List.Perm.length_eq frees_perm]
  grind

@[simp, grind =]
theorem length_toList_iter :
    pool.iter.toList.length = pool.size := by
  simp

@[simp, grind .]
theorem nodup_toList_iter :
    pool.iter.toList.Nodup := by
  simp only [List.Nodup, iter, Std.Iter.toList_filter, List.pairwise_filter]
  apply List.Pairwise.imp ?_ Std.Rco.pairwise_toList_ne
  grind

theorem distinct_toList_iter {idx idx' : Nat} (h : idx < pool.size) (h' : idx' < pool.size)
    (diff : idx ≠ idx') :
      pool.iter.toList[idx] ≠ pool.iter.toList[idx'] := by
  grind [@nodup_toList_iter _ pool, List.pairwise_iff_getElem]

grind_pattern distinct_toList_iter => pool.iter.toList[idx]'_, pool.iter.toList[idx']'_ where
  idx =/= idx'
