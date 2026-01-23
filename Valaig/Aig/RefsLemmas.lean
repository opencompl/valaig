module

public import Valaig.Aig.Refs
import all Valaig.Aig.Refs

public section
namespace Valaig
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
theorem mk_self_eq_self :
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

@[simp]
theorem invert_false :
    lit.invert .false = lit := by
  simp [invert]

@[simp]
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
  by_cases doInvert
  · grind [invert_true]
  · grind [invert_false]

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

section
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

end

end Lit
end Valaig
