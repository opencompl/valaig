module

public import Valaig.Prelude
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

section lemmas

namespace Lit

-- These simp/grind rules are set up to normalize Lit terms to the mk
-- constructor
variable {lit : Lit} {invert : Bool}

@[simp, grind =]
theorem mk_var (var : Var) :
    (Lit.mk var invert).var = var := by
  have : invert.toNat / 2 = 0 := by
    have := Bool.toNat_le invert
    omega
  rw [Lit.var, mk, Nat.or_div_two, this, Nat.or_zero, Nat.mul_div_cancel]
  omega

@[simp, grind =]
theorem mk_inverted (var : Var) :
    (Lit.mk var invert).inverted ↔ invert := by
  simp [mk, inverted]
  decide +revert

@[simp, grind =, local grind! .]
theorem mk_eq_self :
    Lit.mk lit.var lit.inverted = lit := by
  by_cases h : lit.inverted
  · simp_all [mk, var, inverted, ext_idx]
    have {a b : Nat} : a = b ↔ (a % 2) = (b % 2) ∧ (a / 2) = (b / 2) := by omega
    rw [this]
    simp [h, Nat.or_div_two]
  · simp_all [mk, var, inverted, Nat.div_mul_self_eq_mod_sub_self]

theorem ext {lit lit' : Lit} :
    lit = lit' ↔ (lit.var = lit'.var ∧ lit.inverted = lit'.inverted) := by
  grind

@[simp, grind =]
theorem mk_ext {var var' : Var} {invert invert' : Bool} :
    (mk var invert = mk var' invert') ↔ (var = var' ∧ invert = invert') := by
  simp [ext]

@[simp, grind =]
theorem constant_def :
    constant invert = mk .constant invert := by
  rw [constant]

@[simp, grind =]
theorem false_def :
    false = constant .false := by
  rw [false]

@[simp, grind =]
theorem true_def :
    true = constant .true := by
  rw [true]

@[simp, grind =]
theorem isConstant_def :
    lit.isConstant ↔ lit.var = .constant := by
  rw [isConstant]

@[simp, grind =]
theorem isFalse_def :
    lit.isFalse ↔ lit = false := by
  rw [isFalse]

@[simp, grind =]
theorem isTrue_def :
    lit.isTrue ↔ lit = true := by
  rw [isTrue]

theorem isConstant_iff :
    lit.isConstant ↔ lit.isFalse ∨ lit.isTrue := by
  grind

@[simp, local grind =]
theorem invert_false :
    lit.invert .false = lit := by
  simp [invert]

@[simp, local grind =]
theorem invert_true :
    lit.invert .true = mk lit.var ¬lit.inverted := by
  rw [Lit.ext]
  simp [invert]
  constructor
  · simp [var, Nat.xor_div_two]
  · simp [inverted]

@[simp, grind =]
theorem invert_def {doInvert : Bool} :
    lit.invert doInvert = mk lit.var (lit.inverted ≠ doInvert) := by
  simp; grind

@[simp, grind =]
theorem strip_def :
    lit.strip = mk lit.var .false := by
  rw [strip, Lit.ext] <;> simp
  constructor
  · simp [var, Nat.xor_div_two]
  · simp [inverted]

open Std.Sat.AIG in
@[simp, grind =]
theorem ofFanin_def (fi : Fanin) :
    ofFanin fi = mk (.ofIdx fi.gate) fi.invert := by
  rw [ext]
  unfold ofFanin Fanin.gate Fanin.invert mk var inverted
  simp [Nat.or_div_two]
  constructor
  · conv =>
      pattern Bool.toNat _ / 2
      rw [Nat.div_eq_of_lt]
      · skip
      · apply Bool.toNat_lt
    rw [Nat.or_zero]
  · grind only [Bool.toNat_true, Bool.toNat_false]

section ref
variable {α} [DecidableEq α] [Hashable α] {aig : Std.Sat.AIG α}

@[simp, grind =]
theorem ofRef_def (ref : aig.Ref) :
    ofRef ref = mk (.ofRef ref) ref.invert := by
  rw [ofRef]

@[simp, grind =]
theorem toRef_gate {h : lit.var.idx < aig.decls.size} :
    (toRef lit h).gate = lit.var.idx := by
  rw [toRef]

@[simp, grind =]
theorem toRef_invert {h : lit.var.idx < aig.decls.size} :
    (toRef lit h).invert = lit.inverted := by
  simp [toRef]

end ref
end Lit
end lemmas
