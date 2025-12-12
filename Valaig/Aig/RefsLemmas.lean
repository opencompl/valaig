import Valaig.Aig.Refs

namespace Valaig

namespace Var

variable {α} [DecidableEq α] [Hashable α] {aig : Std.Sat.AIG α}
@[simp, grind =]
theorem ofRef_idx (ref : aig.Ref) :
    (ofRef ref).idx = ref.gate := by
  simp only [ofRef]

end Var

namespace Lit
variable {lit : Lit} {invert : Bool}

-- These simp/grind rules are set up to normalize Lit terms to the mk
-- constructor

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

theorem ext_idx (lit lit' : Lit) :
    lit = lit' ↔ lit.idx = lit'.idx := by
  grind only [Lit]

@[grind! .]
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

@[simp, grind =]
theorem invert_def :
    lit.invert = mk lit.var ¬lit.inverted := by
  rw [Lit.ext] <;> simp
  constructor
  · simp [invert, var, Nat.xor_div_two]
  · simp [invert, inverted]

@[simp, grind =]
theorem strip_def :
    lit.strip = mk lit.var .false := by
  rw [strip, Lit.ext] <;> simp
  constructor
  · simp [var, Nat.xor_div_two]
  · simp [inverted]

theorem ofFanin_def (fi : Std.Sat.AIG.Fanin) :
    ofFanin fi = mk (.ofIdx fi.gate) fi.invert := by
  rw [ofFanin]

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
  simp only [toRef, decide_eq_true_eq]

end

end Lit
end Valaig
