module

public import Std.Sat.AIG.Basic

public section
namespace Valaig

/--
Variable: a reference to a node in an Aig based on its index.
-/
structure Var where
  ofIdx ::
    idx : Nat

namespace Var

deriving instance DecidableEq, Repr, Inhabited, BEq, ReflBEq, LawfulBEq for Var

instance : EquivBEq Var := by constructor

@[local grind =_]
theorem ext_idx (var var' : Var) :
    var = var' ↔ var.idx = var'.idx := by
  grind only [Var]

-- Instantiate these directly for inlining
instance : Ord Var where compare := (compare ·.idx ·.idx)

instance : LE Var where le := (·.idx ≤ ·.idx)
instance : DecidableLE Var := fun a b =>
  decidable_of_bool (a.idx ≤ b.idx) (by simp [Var.instLE])

@[local grind =]
theorem le_idx (var var' : Var) :
    var ≤ var' ↔ var.idx ≤ var'.idx := by
  simp [instLE]

instance : Std.IsLinearOrder Var := by
  apply Std.IsLinearOrder.of_le
  <;> constructor
  <;> grind

instance : LT Var where lt := (·.idx < ·.idx)
instance : DecidableLT Var := fun a b =>
  decidable_of_bool (a.idx < b.idx) (by simp [Var.instLT])

@[local grind =]
theorem lt_idx (var var' : Var) :
    var < var' ↔ var.idx < var'.idx := by
  simp [instLT]

instance : Std.LawfulOrderLT Var := by
  apply Std.LawfulOrderLT.of_le
  grind

instance : Min Var := minOfLe

instance : Std.LawfulOrderMin Var := by
  apply Std.LawfulOrderMin.of_le_min_iff
  <;> rw [instMin, minOfLe]
  <;> grind

instance : Max Var := maxOfLe

instance : Std.LawfulOrderMax Var := by
  apply Std.LawfulOrderMax.of_max_le_iff
  <;> rw [instMax, maxOfLe]
  <;> grind

-- Hash the inner value directly to avoid a mixHash use
instance : Hashable Var where hash := (hash ·.idx)
instance : LawfulHashable Var where hash_eq := by simp

@[inline]
def constant : Var :=
  .ofIdx 0

@[inline]
def offset (v : Var) (n : Nat) : Var :=
  .ofIdx (v.idx + n)

@[inline]
def next (v : Var) : Var :=
  v.offset 1

@[inline]
def ofRef {α} [DecidableEq α] [Hashable α] {aig : Std.Sat.AIG α} (ref : aig.Ref) : Var :=
  .ofIdx ref.gate

@[simp, grind! .]
theorem ofRef_idx {α} [DecidableEq α] [Hashable α] {aig : Std.Sat.AIG α} (ref : aig.Ref) :
    (ofRef ref).idx = ref.gate := by
  simp only [ofRef]

end Var

/--
Literal: an invertible reference to a Variable in an Aig.
-/
structure Lit where
  -- TODO: It would be nice to mark this constructor private but the parser uses it currently.
  ofIdx ::
    idx : Nat

namespace Lit

deriving instance DecidableEq, Repr, Inhabited, BEq, ReflBEq, LawfulBEq for Lit

instance : EquivBEq Lit := by constructor

theorem ext_idx (lit lit' : Lit) :
    lit = lit' ↔ lit.idx = lit'.idx := by
  grind only [Lit]

-- Hash the inner value directly to avoid a mixHash use
instance : Hashable Lit where hash := (hash ·.idx)
instance : LawfulHashable Lit where hash_eq := by simp

@[inline]
def mk (v : Var) (invert : Bool := false) : Lit :=
  .ofIdx <| v.idx * 2 ||| invert.toNat

@[inline]
def var (l : Lit) : Var :=
  .ofIdx <| l.idx / 2

@[inline]
def inverted (l : Lit) : Prop :=
  (l.idx &&& 1) ≠ 0
deriving Decidable

@[inline]
def constant (value : Bool) : Lit :=
  mk .constant value

@[inline]
def false : Lit :=
  constant .false

@[inline]
def true : Lit :=
  constant .true

@[inline]
def isConstant (l : Lit) : Prop :=
  l.var = .constant
deriving Decidable

@[inline]
def isFalse (l : Lit) : Prop :=
  l = false
deriving Decidable

@[inline]
def isTrue (l : Lit) : Prop :=
  l = true
deriving Decidable

@[inline]
def invert (l : Lit) (doInvert : Bool := .true) : Lit :=
  if doInvert then
    .ofIdx <| l.idx ^^^ 1
  else
    l

-- Clear inverted
@[inline]
def strip (l : Lit) : Lit :=
  .ofIdx <| l.idx ^^^ (l.idx &&& 1)

-- Currently Lit and Fanin use the same bit stuffing so we can losslessly convert between them
@[inline]
def ofFanin (fi : Std.Sat.AIG.Fanin) : Lit :=
  .ofIdx fi.val

section
variable {α} [DecidableEq α] [Hashable α] {aig : Std.Sat.AIG α}

@[inline]
def ofRef (ref : aig.Ref) : Lit :=
  mk (.ofRef ref) ref.invert

@[inline]
def toRef (lit : Lit) (h : lit.var.idx < aig.decls.size) : aig.Ref :=
  .mk lit.var.idx lit.inverted h

end

end Lit

namespace Var

@[inline, simp]
abbrev toLit (v : Var) (invert : Bool := false) : Lit :=
  .mk v invert

end Var
end Valaig
