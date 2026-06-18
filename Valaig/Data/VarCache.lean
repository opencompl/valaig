module

public import Valaig.Data.Refs
public import Valaig.Data.Nullable
import Valaig.ForLean.Array

public section
namespace Valaig.Data

/--
  An automatically growable cache between contiguous variables and an arbitrary other type.
-/
structure VarCache (α : Type) where
  ofArray ::
    cache : Array α
deriving DecidableEq, Inhabited, Repr

namespace VarCache
variable {α : Type} {cache : VarCache α} {var : Var}

@[inline, local simp, local grind]
def size (cache : VarCache α) : Nat :=
  cache.cache.size

/--
  If the element type is nullable, this returns the number of non-null elements in the cache.
  This method requires iterating the whole array, so is slow and primarily for proofs.
-/
@[expose, local simp, local grind]
def fillSlow [Nullable α] (cache : VarCache α) :=
  cache.cache.countP Nullable.isSome

@[always_inline]
instance instGetElem : GetElem (VarCache α) Var α (fun cache var => var.idx < cache.size) where
  getElem cache var h := cache.cache[var.idx]

@[local simp, local grind =]
private theorem getElem_eq (h : var.idx < cache.size) :
    cache[var]'h = cache.cache[var.idx] := by
  rfl

@[always_inline]
instance instGetElem? : GetElem? (VarCache α) Var α (fun cache var => var.idx < cache.size) where
  getElem? cache var := cache.cache[var.idx]?

instance : LawfulGetElem (VarCache α) Var α (fun cache var => var.idx < cache.size) where
  getElem?_def := by
    simp +instances only [instGetElem?, instGetElem]
    grind

/--
  The membership operator is only defined for nullable caches, where a variable is a member iff
  it references a non-null value in the cache.
-/
instance instMembership [Nullable α] : Membership Var (VarCache α) where
  mem cache var := ∃ (h : var.idx < cache.size), Nullable.isSome (cache[var]'h)

@[local simp, local grind =]
theorem mem_iff [Nullable α] :
    var ∈ cache ↔ ∃ (h : var.idx < cache.size), Nullable.isSome (cache[var]'h) := by
  rfl

@[always_inline]
instance [Nullable α] : Decidable (var ∈ cache) := by
  simp +instances only [instMembership]
  infer_instance

@[simp, grind =]
theorem size_ofArray {arr : Array α} :
    (ofArray arr).size = arr.size := by
  grind

@[simp, grind =]
theorem getElem_ofArray {arr : Array α} (lt : var.idx < (ofArray arr).size) :
    (ofArray arr)[var]'lt = arr[var.idx] := by
  grind

@[inline]
def empty : VarCache α :=
  { cache := #[] }

section empty
attribute [local simp, local grind] empty

@[simp, grind =]
theorem size_empty :
    (empty : VarCache α).size = 0 := by
  grind

@[simp, grind =]
theorem fillSlow_empty [Nullable α] :
    (empty : VarCache α).fillSlow = 0 := by
  grind

@[simp, grind .]
theorem mem_empty [Nullable α] :
    var ∉ (empty : VarCache α) := by
  grind

end empty

@[inline]
def emptyWithCapacity (upTo : Var) : VarCache α :=
  { cache := .emptyWithCapacity (upTo.idx + 1) }

section emptyWithCapacity
variable {upTo : Var}
attribute [local simp, local grind] emptyWithCapacity

@[simp, grind =]
theorem size_emptyWithCapacity :
    (emptyWithCapacity upTo : VarCache α).size = 0 := by
  grind

@[simp, grind =]
theorem fillSlow_emptyWithCapacity [Nullable α] :
    (emptyWithCapacity upTo : VarCache α).fillSlow = 0 := by
  grind

@[simp, grind .]
theorem mem_emptyWithCapacity [Nullable α] :
    var ∉ (emptyWithCapacity upTo : VarCache α) := by
  grind

end emptyWithCapacity

@[inline]
def toArray (cache : VarCache α) : Array α :=
  cache.cache

section toArray
attribute [local simp, local grind] toArray

@[simp, grind =]
theorem size_toArray :
    cache.toArray.size = cache.size := by
  grind

@[simp, grind =]
theorem getElem_toArray (h : var.idx < cache.toArray.size) :
    cache.toArray[var.idx]'h = cache[var] := by
  grind

theorem fillSlow_eq [Nullable α] :
    cache.fillSlow = cache.toArray.countP Nullable.isSome := by
  grind

end toArray

@[inline]
def push (cache : VarCache α) (value : α) : VarCache α :=
  { cache with cache := cache.cache.push value }

section push
variable {value : α}
attribute [local simp, local grind] push

@[simp, grind =]
theorem size_push :
    (cache.push value).size = cache.size + 1 := by
  grind

@[simp, grind =]
theorem fillSlow_push [null : Nullable α] :
    (cache.push value).fillSlow = cache.fillSlow + if null.isSome value then 1 else 0 := by
  grind [Array.countP_push]

@[simp, grind =]
theorem mem_push [null : Nullable α] :
    var ∈ cache.push value ↔
    var ∈ cache ∨ (null.isSome value ∧ var.idx = cache.size) := by
  grind

@[simp, grind =]
theorem getElem_push (lt : var.idx < (cache.push value).size) :
    (cache.push value)[var]'lt =
    if _ : var.idx = cache.size then value else cache[var] := by
  grind

end push

@[inline]
def set (cache : VarCache α) (var : Var) (value : α) (lt : var.idx < cache.size := by grind) : VarCache α :=
  { cache with cache := cache.cache.set var.idx value lt }

section set
variable {value : α} (lt : var.idx < cache.size)
attribute [local simp, local grind] set

@[simp, grind =]
theorem size_set :
    (cache.set var value lt).size = cache.size := by
  grind

@[simp, grind =]
theorem fillSlow_set [null : Nullable α] :
    (cache.set var value lt).fillSlow =
    cache.fillSlow - (if var ∈ cache then 1 else 0) + (if null.isSome value then 1 else 0) := by
  grind

@[simp, grind =]
theorem mem_set [null : Nullable α] {var' : Var} :
    var' ∈ cache.set var value lt ↔
    if _ : var' = var then null.isSome value else var' ∈ cache := by
  grind

@[simp, grind =]
theorem getElem_set {var' : Var} (lt' : var'.idx < (cache.set var value mem).size) :
    (cache.set var value lt)[var']'lt' =
    if _ : var' = var then value else cache[var'] := by
  grind

end set

@[inline]
def modify (cache : VarCache α) (var : Var) (lt : var.idx < cache.size := by grind) (f : { val : α // cache[var] = val } -> α) : VarCache α :=
  { cache with cache := cache.cache.modifyMem var.idx lt f }

section modify
variable {lt : var.idx < cache.size} {f : { val : α // cache[var] = val } -> α}
attribute [local simp, local grind] modify

@[simp, grind =]
theorem size_modify :
    (cache.modify var lt f).size = cache.size := by
  grind

@[simp, grind =]
theorem fillSlow_modify [null : Nullable α] :
    (cache.modify var lt f).fillSlow =
    cache.fillSlow - (if var ∈ cache then 1 else 0) + (if null.isSome (f ⟨cache[var], by grind⟩) then 1 else 0) := by
  simp only [modify, fillSlow, Array.countP_modifyMem, Nullable.isSome_eq]
  cases decide (var ∈ cache) <;> cases null.isNull (f ⟨cache[var], by grind⟩)
  <;> grind

@[simp, grind =]
theorem mem_modify [null : Nullable α] {var' : Var} :
    var' ∈ cache.modify var lt f ↔
    if _ : var' = var then null.isSome (f ⟨cache[var'], by grind⟩) else var' ∈ cache := by
  grind

@[simp, grind =]
theorem getElem_modify {var' : Var} (lt' : var'.idx < (cache.modify var lt f).size) :
    (cache.modify var lt f)[var']'lt' =
    if _ : var' = var then f ⟨cache[var'], by grind⟩ else cache[var'] := by
  grind

end modify

def insertAbove [Nullable α] (cache : VarCache α) (var : Var) (value : α)
  (le : cache.size ≤ var.idx := by grind) (some : Nullable.isSome value := by grind) : VarCache α :=
  if _ : cache.size = var.idx then
    cache.push value
  else
    cache.push Nullable.null |>.insertAbove var value
termination_by var.idx - cache.size
decreasing_by grind

section insertAbove
variable [Nullable α] {value : α} (le : cache.size ≤ var.idx) (some : Nullable.isSome value)
attribute [local grind] insertAbove

@[simp, grind =]
theorem size_insertAbove :
    (cache.insertAbove var value le some).size = var.idx + 1 := by
  fun_induction insertAbove <;> grind

@[simp, grind =]
theorem fillSlow_insertAbove :
    (cache.insertAbove var value le some).fillSlow =
    cache.fillSlow + 1 := by
  fun_induction insertAbove <;> grind

@[simp, grind =]
theorem mem_insertAbove {var' : Var} :
    var' ∈ cache.insertAbove var value le some ↔
    var' ∈ cache ∨ var' = var := by
  fun_induction insertAbove <;> grind

@[simp, grind =]
theorem getElem_insertAbove {var' : Var} (lt : var'.idx < (cache.insertAbove var value le).size) :
    (cache.insertAbove var value le some)[var']'lt =
    if var' = var then
      value
    else if h : var'.idx < cache.size then
      cache[var']'h
    else
      Nullable.null := by
  fun_induction insertAbove <;> grind

end insertAbove

@[inline]
def insert [Nullable α] (cache : VarCache α) (var : Var) (value : α)
  (some : Nullable.isSome value := by grind) : VarCache α :=
  if _ : var.idx < cache.size then
    cache.set var value
  else
    cache.insertAbove var value

section insert
variable [Nullable α] {value : α} (some : Nullable.isSome value)
attribute [local simp, local grind] insert

@[simp, grind =]
theorem size_insert :
    (cache.insert var value some).size = max cache.size (var.idx + 1) := by
  grind

@[simp, grind =]
theorem fillSlow_insert :
    (cache.insert var value some).fillSlow =
    cache.fillSlow + (if var ∈ cache then 0 else 1) := by
  split
  · have : cache.fillSlow > 0 := by simp only [fillSlow, Array.countP_pos_iff]; grind
    grind
  · grind

@[simp, grind =]
theorem mem_insert {var' : Var} :
    var' ∈ cache.insert var value some ↔
    var' ∈ cache ∨ var' = var := by
  grind

@[simp, grind =]
theorem getElem_insert {var' : Var} (lt : var'.idx < (cache.insert var value).size) :
    (cache.insert var value some)[var']'lt =
    if var' = var then
      value
    else if h : var'.idx < cache.size then
      cache[var']'h
    else
      Nullable.null := by
  grind

end insert

@[inline]
def erase [Nullable α] (cache : VarCache α) (var : Var) : VarCache α :=
  if _ : var.idx < cache.size then
    cache.set var Nullable.null
  else
    cache

section erase
variable [Nullable α]
attribute [local simp, local grind] erase

@[simp, grind =]
theorem size_erase :
    (cache.erase var).size = cache.size := by
  grind

@[simp, grind =]
theorem fillSlow_erase :
    (cache.erase var).fillSlow =
    cache.fillSlow - if var ∈ cache then 1 else 0 := by
  grind

@[simp, grind =]
theorem mem_erase {var' : Var} :
    var' ∈ cache.erase var ↔ var' ∈ cache ∧ var' ≠ var := by
  grind

@[simp, grind =]
theorem getElem_erase {var' : Var} (lt : var'.idx < (cache.erase var).size) :
    (cache.erase var)[var']'lt =
    if var' = var then
      Nullable.null
    else
      have h : var'.idx < cache.size := by grind
      cache[var']'h := by
  grind

end erase

@[inline]
def mapLit (cache : VarCache Lit) (lit : Lit) (lt : lit.var.idx < cache.size := by grind [Var.lt_idx]) : Lit :=
  lit.mapTo cache[lit.var]

section mapLit
variable {cache : VarCache Lit} {lit : Lit} (lt : lit.var.idx < cache.size)
attribute [local simp, local grind] mapLit

@[simp, grind =]
theorem var_mapLit :
    (cache.mapLit lit lt).var = cache[lit.var].var := by
  grind

@[simp, grind =]
theorem inverted_mapLit :
    (cache.mapLit lit lt).inverted = (lit.inverted ≠ cache[lit.var].inverted) := by
  grind

end mapLit

end VarCache
end Valaig.Data
