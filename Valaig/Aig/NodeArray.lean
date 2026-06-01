module

public import Valaig.Refs

public section
namespace Valaig.Aig

/--
  The internal datastructure used to define an array of nodes in the Aig.
  This is an implementation detail and should not be relied upon.
-/
structure NodeArray where
  _nodes : Array Lit
  nonempty : _nodes.size > 0 := by grind
  pairs : 2 ∣ _nodes.size := by grind
deriving Repr, DecidableEq

namespace NodeArray
variable {var : Var} {arr : NodeArray}

attribute [local grind .] NodeArray.pairs
attribute [local grind! .] NodeArray.nonempty

@[grind .]
theorem two_dvd_nodes_size :
    2 ∣ arr._nodes.size := by
  grind

@[always_inline, local simp, local grind]
def size (arr : NodeArray) : Nat :=
  arr._nodes.size / 2

@[simp, grind! .]
theorem zero_lt_size :
    0 < arr.size := by
  grind

instance : Membership Var NodeArray where
  mem arr var := var.idx < arr.size

@[simp, grind =]
theorem mem_iff :
    var ∈ arr ↔ var.idx < arr.size := by
  rfl

@[always_inline]
instance : Decidable (var ∈ arr) :=
  decidable_of_iff' _ mem_iff

structure Elem where
  arr : NodeArray
  idx : Nat
  valid : idx < arr._nodes.size := by grind
  dvd : 2 ∣ idx := by grind

attribute [local grind .] Elem.dvd
attribute [local grind! .] Elem.valid

@[always_inline]
instance instGetElem : GetElem NodeArray Var Elem Membership.mem where
  getElem arr var h := .mk arr (2 * var.idx)

@[simp, grind =]
private theorem arr_getElem (mem : var ∈ arr) :
  (arr[var]'mem).arr = arr := by
  simp +instances [GetElem.getElem]

namespace Elem
variable {elem : Elem}

@[always_inline]
def fst (elem : Elem) : Lit :=
  elem.arr._nodes[elem.idx]

@[always_inline]
def snd (elem : Elem) : Lit :=
  elem.arr._nodes[elem.idx + 1]

@[coe, always_inline]
def toPair (elem : Elem) : (Lit × Lit) :=
  (elem.fst, elem.snd)

@[always_inline]
instance : Coe Elem (Lit × Lit) where
  coe := Elem.toPair

@[simp, grind =]
theorem fst_eq :
    elem.fst = elem.toPair.fst := by
  grind [toPair]

@[simp, grind =]
theorem snd_eq :
    elem.snd = elem.toPair.snd := by
  grind [toPair]

end Elem

attribute [local grind] Elem.toPair Elem.fst Elem.snd

@[local simp, local grind =]
private theorem fst_toPair_getElem (mem : var ∈ arr) :
    (arr[var]'mem).toPair.fst = arr._nodes[2 * var.idx] := by
  simp only [Elem.toPair, Elem.fst, instGetElem]

@[local simp, local grind =]
private theorem snd_toPair_getElem (mem : var ∈ arr) :
    (arr[var]'mem).toPair.snd = arr._nodes[2 * var.idx + 1] := by
  simp only [Elem.toPair, Elem.snd, instGetElem]

@[always_inline]
def empty : NodeArray :=
  .mk #[.false, .false]

@[simp, grind =]
theorem size_empty :
    empty.size = 1 := by
  grind [empty]

@[simp, grind =]
theorem getElem_empty (mem : var ∈ empty) :
    (empty[var]'mem).toPair = (.false, .false) := by
  grind [empty]

@[inline]
instance : Inhabited NodeArray where
  default := empty

@[always_inline]
def push (arr : NodeArray) (fst snd : Lit) : NodeArray :=
  .mk (arr._nodes.push fst |>.push snd)

@[simp, grind =]
theorem size_push {fst snd : Lit} :
    (arr.push fst snd).size = arr.size + 1 := by
  grind [push]

@[simp, grind =]
theorem getElem_push {fst snd : Lit} (mem : var ∈ (arr.push fst snd)) :
    ((arr.push fst snd)[var]'mem).toPair =
    if _ : var ∈ arr then arr[var].toPair else (fst, snd) := by
  grind [push]

@[always_inline]
def set (arr : NodeArray) (var : Var) (fst snd : Lit) (mem : var ∈ arr := by get_elem_tactic) : NodeArray :=
  let baseIdx := 2 * var.idx
  .mk (arr._nodes.set baseIdx fst |>.set (baseIdx + 1) snd)

@[simp, grind =]
theorem size_set (mem : var ∈ arr) {fst snd : Lit} :
    (arr.set var fst snd mem).size = arr.size := by
  grind [set]

@[simp, grind =]
theorem getElem_set {fst snd : Lit} {var' : Var} (mem : var ∈ arr) (mem' : var' ∈ arr.set var fst snd mem) :
    (arr.set var fst snd mem)[var']'mem' =
    if var' = var then
      (fst, snd)
    else
      have h : var' ∈ arr := by grind
      (arr[var']'h).toPair := by
  grind [set]

end NodeArray
