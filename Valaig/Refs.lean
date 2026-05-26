module

public import Valaig.Prelude
public import Std.Sat.AIG.Basic

public section
namespace Valaig

/--
Variable: a reference to a node in an Aig based on its index.

These have contiguous indices, with the constant variable (taken to be `false` if not inverted)
represented by index 0. Where possible, users should prefer dealing directly with `Var` rather
than accessing the underlying index with `Var.idx`. The primary use for direct access to the index
is for indexing into contiguous memory (`Array`s).
-/
@[ext, grind ext]
structure Var where
  ofIdx ::
    idx : Nat

namespace Var
variable {var : Var}

@[simp]
theorem ofIdx_idx :
    .ofIdx var.idx = var := by
  grind

deriving instance DecidableEq, Repr, Inhabited, BEq, ReflBEq, LawfulBEq for Var

instance : EquivBEq Var := by constructor

-- Instantiate these directly for inlining
instance : Ord Var where compare := (compare ·.idx ·.idx)

instance : LE Var where le := (·.idx ≤ ·.idx)
instance : DecidableLE Var := fun a b =>
  decidable_of_bool (a.idx ≤ b.idx) (by simp +instances [Var.instLE])

theorem le_idx (var var' : Var) :
    var ≤ var' ↔ var.idx ≤ var'.idx := by
  simp +instances [instLE]

instance : Std.IsLinearOrder Var := by
  apply Std.IsLinearOrder.of_le
  <;> constructor
  <;> grind [le_idx]

instance : LT Var where lt := (·.idx < ·.idx)
instance : DecidableLT Var := fun a b =>
  decidable_of_bool (a.idx < b.idx) (by simp +instances [Var.instLT])

theorem lt_idx (var var' : Var) :
    var < var' ↔ var.idx < var'.idx := by
  simp +instances [instLT]

grind_pattern le_idx => var.idx, var'.idx, var ≤ var'
grind_pattern le_idx => var.idx, var'.idx, var > var'
grind_pattern lt_idx => var.idx, var'.idx, var < var'
grind_pattern lt_idx => var.idx, var'.idx, var ≥ var'

instance : Std.LawfulOrderLT Var := by
  apply Std.LawfulOrderLT.of_le
  grind [lt_idx]

instance : WellFoundedRelation Var where
  rel := (· < ·)
  wf := by
    constructor
    have {var : Var} : Acc (· < ·) var := by
      induction h : var.idx generalizing var
      <;> grind [Acc, lt_idx]
    apply this

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

@[simp, grind =]
theorem idx_constant :
    constant.idx = 0 := by
  simp [constant]

theorem constant_iff_idx_zero :
    var = constant ↔ var.idx = 0 := by
  grind

/--
Adding a `Nat` to a `Var` increments the `Var`'s index.
-/
@[inline]
instance : HAdd Var Nat Var where
  hAdd (var : Var) (n : Nat) :=
    .ofIdx (var.idx + n)

@[simp, grind =]
theorem idx_add {n : Nat} :
    (var + n).idx = var.idx + n := by
  simp [HAdd.hAdd]

@[inline]
def ofRef {α} [DecidableEq α] [Hashable α] {aig : Std.Sat.AIG α} (ref : aig.Ref) : Var :=
  .ofIdx ref.gate

@[simp, grind =]
theorem idx_ofRef {α} [DecidableEq α] [Hashable α] {aig : Std.Sat.AIG α} (ref : aig.Ref) :
    (ofRef ref).idx = ref.gate := by
  simp only [ofRef]

end Var

/--
Literal: an invertible reference to a `Var` in an `Aig`.

These are represented by storing the inversion in the least significant bit and the variable
left-shifted by one in the higher bits. Although this detail is exposed for use with contiguous
containers, care should be taken to avoid relying on it whenever possible.
-/
@[ext, local grind ext]
structure Lit where
  ofIdx ::
    idx : Nat

namespace Lit
variable {lit : Lit}

deriving instance DecidableEq, Repr, Inhabited, BEq, ReflBEq, LawfulBEq for Lit
instance : EquivBEq Lit := by constructor

-- Hash the inner value directly to avoid a mixHash use
instance : Hashable Lit where hash := (hash ·.idx)
instance : LawfulHashable Lit where hash_eq := by simp

/--
Returns the variable referenced by a literal.
-/
@[inline, local grind]
def var (lit : Lit) : Var :=
  -- TODO(u32): Switch to left shift
  .ofIdx <| lit.idx / 2

@[simp]
theorem idx_lt_of_var_lt {lit' : Lit} (lt : lit.var < lit'.var) :
    lit.idx < lit'.idx := by
  grind only [var, Var.lt_idx]

grind_pattern idx_lt_of_var_lt => lit.idx, lit.var < lit'.var
grind_pattern idx_lt_of_var_lt => lit'.idx, lit.var < lit'.var
grind_pattern idx_lt_of_var_lt => lit.idx, lit.var ≥ lit'.var
grind_pattern idx_lt_of_var_lt => lit'.idx, lit.var ≥ lit'.var

/--
Returns the whether the literal is inverted.
-/
@[local grind]
def inverted (lit : Lit) : Prop :=
  (lit.idx % 2) ≠ 0

@[inline]
instance {l : Lit} : Decidable l.inverted :=
  have : (l.idx.toUInt8 &&& 1) = 1 ↔ l.inverted := by
    simp [inverted, ←UInt8.toNat_inj]
  decidable_of_iff _ this

@[ext, grind ext]
theorem ext_of {lit lit' : Lit} (var : lit.var = lit'.var) (inverted : lit.inverted = lit'.inverted) :
    lit = lit' := by
  grind [Lit.var, Lit.inverted]

theorem idx_eq :
    lit.idx = lit.var.idx * 2 + (decide lit.inverted).toNat := by
  grind [Bool.toNat_lt, Nat.shiftLeft_eq]

@[grind =]
theorem idx_eq_cases {lit : Lit} :
    lit.idx =
    if lit.inverted then
      lit.var.idx * 2 + 1
    else
      lit.var.idx * 2 := by
  grind

/--
Returns a literal referencing a variable which is optionally inverted.
-/
@[inline]
def mk (var : Var) (invert : Bool := false) : Lit :=
  .ofIdx <| var.idx * 2 ||| invert.toNat

@[simp, grind =]
theorem var_mk {var : Var} {invert : Bool} :
    (mk var invert).var = var := by
  have : invert.toNat / 2 = 0 := by grind only [Bool.toNat_le invert]
  grind only [mk, Lit.var, Nat.or_div_two, Nat.shiftLeft_eq]

@[simp, grind =]
theorem inverted_mk {var : Var} {invert : Bool} :
    (mk var invert).inverted = invert := by
  unfold mk inverted
  by_cases invert <;> simp_all

/--
Returns the constant literal of specified value.
-/
@[inline, coe]
def constant (value : Bool) : Lit :=
  .ofIdx value.toNat

@[simp]
theorem var_constant {value : Bool} :
    (constant value).var = .constant := by
  cases value <;> grind [constant]

@[simp]
theorem inverted_constant {value : Bool} :
    (constant value).inverted = value := by
  grind [constant]

@[grind =]
theorem constant_eq {value : Bool} :
    (constant value) = .mk .constant value := by
  grind [var_constant, inverted_constant]

@[simp, grind =]
theorem idx_constant {value : Bool} :
    (constant value).idx = value.toNat := by
  grind

@[inline]
instance : Coe Bool Lit where
  coe := constant

/--
The (single) false literal.
To determine if a literal is false it suffices to check for equality with this.
-/
@[inline]
def false : Lit :=
  .ofIdx 0

@[simp ←, grind =]
theorem false_eq :
    false = constant .false := by
  simp [constant, false]

@[simp]
theorem var_false :
    false.var = .constant := by
  grind

@[simp]
theorem inverted_false :
    ¬false.inverted := by
  grind

@[simp]
theorem idx_false :
    false.idx = 0 := by
  grind

/--
The (single) true literal.
To determine if a literal is true it suffices to check for equality with this.
-/
@[inline]
def true : Lit :=
  .ofIdx 1

@[simp ←, grind =]
theorem true_eq :
    true = constant .true := by
  simp [constant, true]

@[simp]
theorem var_true :
    true.var = .constant := by
  grind

@[simp]
theorem inverted_true :
    true.inverted := by
  grind

@[simp]
theorem idx_true :
    true.idx = 1 := by
  grind

/--
True iff the literal references a constant.
-/
def isConstant (lit : Lit) : Prop :=
  lit.var = .constant

@[inline]
instance {l : Lit} : Decidable l.isConstant :=
  have : l.idx < 2 ↔ l.isConstant := by
    simp [isConstant, Var.constant, var]
  decidable_of_iff _ this

@[simp, grind =]
theorem isConstant_iff :
    lit.isConstant ↔ lit = constant lit.inverted := by
  grind [isConstant]

@[simp, grind .]
theorem isConstant_true :
    true.isConstant := by
  simp

@[simp, grind .]
theorem isConstant_false :
    false.isConstant := by
  simp

theorem isConstant_iff_eq_false_or_eq_true :
    lit.isConstant ↔ lit = false ∨ lit = true := by
  grind

/--
Returns `some` of the constant value if the literal references a constant, or
otherwise `none`.
-/
@[inline]
def asConstant (lit : Lit) : Option Bool :=
  if lit.isConstant then
    -- Comparing to 1 seems to avoid a branch. We use toUInt8 to prevent
    -- checking for boxing
    some (lit.idx.toUInt8 = 1)
  else
    none

@[simp]
theorem asConstant_false_iff :
    lit.asConstant = some .false ↔ lit = .false := by
  by_cases lit.inverted
  · simp_all [asConstant]; grind
  · simp_all [asConstant]

@[simp]
theorem asConstant_true_iff :
    lit.asConstant = some .true ↔ lit = .true := by
  by_cases lit.inverted
  · simp_all [asConstant]
  · simp_all [asConstant]; grind

@[simp]
theorem asConstant_none_iff :
    lit.asConstant = none ↔ ¬lit.isConstant:= by
  simp [asConstant]

@[grind =]
theorem asConstant_eq :
    lit.asConstant =
    if lit = false then
      some .false
    else if lit = true then
      some .true
    else
      none := by
  grind [asConstant_false_iff, asConstant_true_iff, asConstant_none_iff]

/--
Optionally inverts the polarity of a literal.
-/
@[inline]
def invert (lit : Lit) (doInvert : Bool := .true) : Lit :=
  .ofIdx <| lit.idx ^^^ doInvert.toNat

@[simp]
theorem inverted_invert_false :
    (lit.invert .false).inverted = lit.inverted := by
  simp [invert]

@[simp]
theorem inverted_invert_true :
    (lit.invert .true).inverted = ¬lit.inverted := by
  simp [invert, inverted]

@[simp]
theorem inverted_invert {doInvert : Bool} :
    (lit.invert doInvert).inverted = (doInvert ≠ lit.inverted) := by
  cases doInvert <;> simp

@[simp]
theorem var_invert {doInvert : Bool} :
    (lit.invert doInvert).var = lit.var := by
  simp only [invert, var, Nat.xor_div_two]
  cases doInvert <;> simp

@[grind =]
theorem invert_eq {doInvert : Bool} :
    lit.invert doInvert = .mk lit.var (doInvert ^^ lit.inverted) := by
  grind [var_invert, inverted_invert]

/--
Sets a literal's polarity to false.
This implementation is more efficient than using `Lit.mk l.var false`.
-/
@[inline]
def strip (lit : Lit) : Lit :=
  -- TODO(u32): Switch this to bit clearing
  .ofIdx <| lit.idx ^^^ (lit.idx &&& 1)

@[simp]
theorem var_strip :
    lit.strip.var = lit.var := by
  simp [strip, var, Nat.xor_div_two]

@[simp]
theorem inverted_strip :
    ¬lit.strip.inverted := by
  simp [strip, inverted]

@[grind =]
theorem strip_eq :
    lit.strip = .mk lit.var .false := by
  grind [var_strip, inverted_strip]

/--
Maps the literal's variable to a new literal, before inverting the new literal if the
original was also inverted.
-/
@[inline]
def mapTo (lit new : Lit) : Lit :=
  new.invert lit.inverted

@[simp]
theorem var_mapTo {new : Lit} :
    (lit.mapTo new).var = new.var := by
  simp [mapTo]

@[simp]
theorem inverted_mapTo {new : Lit} :
    (lit.mapTo new).inverted = (new.inverted ≠ lit.inverted) := by
  grind [mapTo]

@[grind =]
theorem mapTo_eq {new : Lit} :
    lit.mapTo new = .mk new.var (new.inverted ≠ lit.inverted) := by
  grind [var_mapTo, inverted_mapTo]

/--
Replaces the literal's variable to a literal with a new variable, keeping the inversion.
-/
@[inline]
def mapToVar (lit : Lit) (var : Var) : Lit :=
  mk var lit.inverted

@[simp]
theorem var_mapToVar {var : Var} :
    (lit.mapToVar var).var = var := by
  simp [mapToVar]

@[simp]
theorem inverted_mapToVar {var : Var} :
    (lit.mapToVar var).inverted = lit.inverted := by
  simp [mapToVar]

@[grind =]
theorem mapToVar_eq {var : Var} :
    lit.mapToVar var = .mk var lit.inverted := by
  grind [var_mapToVar, inverted_mapToVar]

@[inline]
def ofFanin (fi : Std.Sat.AIG.Fanin) : Lit :=
  -- Currently Lit and Fanin use the same bit stuffing so we can losslessly
  -- convert between them
  .ofIdx fi.val

@[simp]
theorem var_ofFanin {fi : Std.Sat.AIG.Fanin} :
    (ofFanin fi).var = .ofIdx fi.gate := by
  simp [ofFanin, Std.Sat.AIG.Fanin.gate, var]

@[simp]
theorem inverted_ofFanin {fi : Std.Sat.AIG.Fanin} :
    (ofFanin fi).inverted = fi.invert := by
  simp [ofFanin, Std.Sat.AIG.Fanin.invert, inverted]

@[grind =]
theorem ofFanin_eq {fi : Std.Sat.AIG.Fanin} :
    ofFanin fi = .mk (.ofIdx fi.gate) fi.invert := by
  grind [var_ofFanin, inverted_ofFanin]

@[inline]
def toFanin (lit : Lit) : Std.Sat.AIG.Fanin :=
  .ofRaw lit.idx

open Std.Sat.AIG in
@[simp, grind =]
theorem gate_toFanin :
    lit.toFanin.gate = lit.var.idx := by
  simp [toFanin, Fanin.gate, var]

open Std.Sat.AIG in
@[simp, grind =]
theorem invert_toFanin :
    lit.toFanin.invert = lit.inverted := by
  simp [toFanin, Fanin.invert, inverted]

@[simp, grind =]
theorem toFanin_ofFanin {fi : Std.Sat.AIG.Fanin} :
    (Lit.ofFanin fi).toFanin = fi := by
  simp [ofFanin, toFanin]

@[simp, grind =]
theorem ofFanin_toFanin :
    Lit.ofFanin lit.toFanin = lit := by
  simp [ofFanin, toFanin]

section
variable {α} [DecidableEq α] [Hashable α] {aig : Std.Sat.AIG α}

@[inline]
def ofRef (ref : aig.Ref) : Lit :=
  mk (.ofRef ref) ref.invert

@[simp]
theorem var_ofRef (ref : aig.Ref) :
    (ofRef ref).var = (.ofRef ref) := by
  simp [ofRef]

@[simp]
theorem inverted_ofRef (ref : aig.Ref) :
    (ofRef ref).inverted = ref.invert := by
  simp [ofRef]

@[simp, grind =]
theorem ofRef_eq (ref : aig.Ref) :
    ofRef ref = .mk (.ofRef ref) ref.invert := by
  grind [var_ofRef, inverted_ofRef]

@[inline]
def toRef (lit : Lit) (h : lit.var.idx < aig.decls.size) : aig.Ref :=
  .mk lit.var.idx lit.inverted h

@[simp, grind =]
theorem gate_toRef (h : lit.var.idx < aig.decls.size) :
    (toRef lit h).gate = lit.var.idx := by
  rw [toRef]

@[simp]
theorem invert_toRef_eq_true (h : lit.var.idx < aig.decls.size) :
    (toRef lit h).invert = lit.inverted := by
  simp [toRef]

@[simp, grind =]
theorem invert_toRef (h : lit.var.idx < aig.decls.size) :
    (toRef lit h).invert = decide lit.inverted := by
  simp [toRef]

@[simp, grind =]
theorem toRef_ofRef (ref : aig.Ref) :
    toRef (ofRef ref) (by grind [ref.hgate]) = ref := by
  simp [toRef]

end

end Lit

@[inline, expose, reducible, simp, grind unfold]
def Var.toLit (var : Var) (invert : Bool := false) : Lit :=
  .mk var invert

@[inline]
instance : Coe Var Lit where
  coe := Var.toLit

end Valaig
