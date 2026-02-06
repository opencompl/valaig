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
  decidable_of_bool (a.idx ≤ b.idx) (by simp +instances [Var.instLE])

@[local grind =]
theorem le_idx (var var' : Var) :
    var ≤ var' ↔ var.idx ≤ var'.idx := by
  simp +instances [instLE]

instance : Std.IsLinearOrder Var := by
  apply Std.IsLinearOrder.of_le
  <;> constructor
  <;> grind

instance : LT Var where lt := (·.idx < ·.idx)
instance : DecidableLT Var := fun a b =>
  decidable_of_bool (a.idx < b.idx) (by simp +instances [Var.instLT])

@[local grind =]
theorem lt_idx (var var' : Var) :
    var < var' ↔ var.idx < var'.idx := by
  simp +instances [instLT]

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

theorem constant_idx_eq_zero :
    constant.idx = 0 := by
  simp [constant]

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
Literal: an invertible reference to a `Variable` in an `Aig`.
-/
structure Lit where
  -- TODO: It would be nice to mark this constructor private but the parser uses it currently.
  ofIdx ::
    idx : Nat

namespace Lit
variable {lit : Lit}

deriving instance DecidableEq, Repr, Inhabited, BEq, ReflBEq, LawfulBEq for Lit
instance : EquivBEq Lit := by constructor

theorem ext_idx (lit lit' : Lit) :
    lit = lit' ↔ lit.idx = lit'.idx := by
  grind only [Lit]

-- Hash the inner value directly to avoid a mixHash use
instance : Hashable Lit where hash := (hash ·.idx)
instance : LawfulHashable Lit where hash_eq := by simp

/--
Returns a literal referencing a variable which is optionally inverted.
-/
@[inline]
def mk (v : Var) (invert : Bool := false) : Lit :=
  .ofIdx <| v.idx <<< 1 ||| invert.toNat

/--
Returns the variable referenced by a literal.
-/
@[inline]
def var (l : Lit) : Var :=
  -- TODO(u32): Switch to left shift
  .ofIdx <| l.idx / 2

@[simp, grind =]
theorem mk_var (var : Var) (invert: Bool) :
    (Lit.mk var invert).var = var := by
  have : invert.toNat / 2 = 0 := by
    have := Bool.toNat_le invert
    omega
  rw [Lit.var, mk, Nat.or_div_two, this, Nat.or_zero, Nat.shiftLeft_eq, Nat.mul_div_cancel]
  omega

/--
Returns the whether the literal is inverted.
-/
def inverted (l : Lit) : Prop :=
  (l.idx % 2) ≠ 0

@[inline]
instance {l : Lit} : Decidable l.inverted :=
  have : (l.idx.toUInt8 &&& 1) = 1 ↔ l.inverted := by
    simp [inverted, ←UInt8.toNat_inj]
  decidable_of_iff _ this

@[simp, grind .]
theorem mk_inverted (var : Var) (invert : Bool) :
    (Lit.mk var invert).inverted = invert := by
  unfold mk inverted
  by_cases invert <;> simp_all

@[simp, grind =, local grind! .]
theorem mk_eq_self :
    Lit.mk lit.var lit.inverted = lit := by
  rw [mk, var, ext_idx]
  by_cases h : lit.inverted
  · simp_all [inverted]; rw [←Nat.shiftLeft_add_eq_or_of_lt] <;> omega
  · simp_all [inverted] <;> omega

theorem ext {lit lit' : Lit} :
    lit = lit' ↔ (lit.var = lit'.var ∧ lit.inverted = lit'.inverted) := by
  grind only [mk_eq_self]

@[simp, grind =]
theorem mk_ext {var var' : Var} {invert invert' : Bool} :
    (mk var invert = mk var' invert') ↔ (var = var' ∧ invert = invert') := by
  simp [ext]

/--
Returns the constant literal of specified value.
-/
@[inline]
def constant (value : Bool) : Lit :=
  .ofIdx value.toNat

@[simp, grind =]
theorem constant_def :
    constant invert = mk .constant invert := by
  simp [constant, mk, Var.constant]

/--
The (single) false literal.
To determine if a literal is false it suffices to check for equality with this.
-/
@[inline]
def false : Lit :=
  .ofIdx 0

@[simp, grind =]
theorem false_def :
    false = constant .false := by
  simp [constant, false]

/--
The (single) true literal.
To determine if a literal is true it suffices to check for equality with this.
-/
@[inline]
def true : Lit :=
  .ofIdx 1

@[simp, grind =]
theorem true_def :
    true = constant .true := by
  simp [constant, true]

/--
True iff the literal references a constant.
-/
@[inline]
def isConstant (l : Lit) : Prop :=
  l.var = .constant

@[inline]
instance {l : Lit} : Decidable l.isConstant :=
  have : l.idx < 2 ↔ l.isConstant := by
    simp [isConstant, Var.constant, Var.ext_idx, var]
  decidable_of_iff _ this

@[simp, grind =]
theorem isConstant_def :
    lit.isConstant ↔ lit.var = .constant := by
  rw [isConstant]

@[simp]
theorem true_isConstant :
    true.isConstant := by
  simp [isConstant]

@[simp]
theorem false_isConstant :
    false.isConstant := by
  simp [isConstant]

theorem isConstant_iff_false_or_true :
    lit.isConstant ↔ lit = false ∨ lit = true := by
  grind

/--
Returns `some` of the constant value if the literal references a constant, or
otherwise `none`.
-/
@[inline]
def asConstant (l : Lit) : Option Bool :=
  if l.isConstant then
    -- Comparing to 1 seems to avoid a branch. We use toUInt8 to prevent
    -- checking for boxing
    some (l.idx.toUInt8 = 1)
  else
    none

@[simp]
theorem asConstant_false :
    lit.asConstant = some .false ↔ lit = .false := by
  simp [asConstant, Var.constant, ext_idx, var, mk, UInt8.ofNat_eq_iff_mod_eq_toNat]
  grind only

@[simp]
theorem asConstant_true :
    lit.asConstant = some .true ↔ lit = .true := by
  simp [asConstant, Var.constant, ext_idx, var, mk, UInt8.ofNat_eq_iff_mod_eq_toNat]
  grind only

@[simp]
theorem asConstant_none :
    lit.asConstant = none ↔ ¬lit.isConstant:= by
  simp [asConstant]

@[grind =]
theorem asConstant_def :
    lit.asConstant =
    if lit = false then
      some .false
    else if lit = true then
      some .true
    else
      none := by
  grind [asConstant_false, asConstant_true, asConstant_none]

/--
Optionally inverts the polarity of a literal.
-/
@[inline]
def invert (l : Lit) (doInvert : Bool := .true) : Lit :=
  .ofIdx <| l.idx ^^^ doInvert.toNat

@[simp, local grind =]
theorem invert_false :
    lit.invert .false = lit := by
  simp [invert]

@[simp, local grind =]
theorem invert_true :
    lit.invert .true = mk lit.var ¬lit.inverted := by
  simp [Lit.ext, invert]
  simp [var, inverted, Nat.xor_div_two]

@[simp, grind =]
theorem invert_def {doInvert : Bool} :
    lit.invert doInvert = mk lit.var (lit.inverted ≠ doInvert) := by
  simp; grind

/--
Sets a literal's polarity to false.
This implementation is more efficient than using `Lit.mk l.var false`.
-/
@[inline]
def strip (l : Lit) : Lit :=
  -- TODO(u32): Switch this to bit clearing
  .ofIdx <| l.idx ^^^ (l.idx &&& 1)

@[simp, grind =]
theorem strip_def :
    lit.strip = mk lit.var .false := by
  rw [strip, Lit.ext] <;> simp
  simp [var, inverted, Nat.xor_div_two]

@[inline]
def ofFanin (fi : Std.Sat.AIG.Fanin) : Lit :=
  -- Currently Lit and Fanin use the same bit stuffing so we can losslessly
  -- convert between them
  .ofIdx fi.val

-- Should we prove this by showing individually that gate and invert map?
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
    simp [Nat.or_zero, Nat.shiftLeft_eq]
  · grind only [Bool.toNat_true, Bool.toNat_false]

section
variable {α} [DecidableEq α] [Hashable α] {aig : Std.Sat.AIG α}

@[inline]
def ofRef (ref : aig.Ref) : Lit :=
  mk (.ofRef ref) ref.invert

@[simp, grind =]
theorem ofRef_def (ref : aig.Ref) :
    ofRef ref = mk (.ofRef ref) ref.invert := by
  rw [ofRef]

@[inline]
def toRef (lit : Lit) (h : lit.var.idx < aig.decls.size) : aig.Ref :=
  .mk lit.var.idx lit.inverted h

@[simp, grind =]
theorem toRef_gate {h : lit.var.idx < aig.decls.size} :
    (toRef lit h).gate = lit.var.idx := by
  rw [toRef]

@[simp, grind =]
theorem toRef_invert {h : lit.var.idx < aig.decls.size} :
    (toRef lit h).invert = lit.inverted := by
  simp [toRef]


end

end Lit

@[inline, simp]
abbrev Var.toLit (v : Var) (invert : Bool := false) : Lit :=
  .mk v invert
