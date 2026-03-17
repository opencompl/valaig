module

public import Valaig.Aig.Basic
import all Valaig.Aig.Basic
public import Valaig.Aig.StdSatLemmas

public section
namespace Valaig.Aig

/--
A pair of Aigs are monotone (represented with `old ≤ new`) if all references valid in the old Aig
are also valid in the new Aig and all getters for these references return the same values
-/
structure Monotone (old new : Aig) : Prop where
  varValid   {var : Var}      (_ : var.validIn old) : var.validIn new
  inputValid {idx : InputIdx} (_ : idx.validIn old) : idx.validIn new
  latchValid {idx : LatchIdx} (_ : idx.validIn old) : idx.validIn new

  get         {var : Var}      (_ : var.validIn old) : new.get var      = old.get var
  inputGetVar {idx : InputIdx} (_ : idx.validIn old) : idx.getVar new   = idx.getVar old
  latchGetVar {idx : LatchIdx} (_ : idx.validIn old) : idx.getVar new   = idx.getVar old
  getNext     {idx : LatchIdx} (_ : idx.validIn old) : idx.getNext new  = idx.getNext old
  getReset    {idx : LatchIdx} (_ : idx.validIn old) : idx.getReset new = idx.getReset old

@[inherit_doc Monotone]
instance : LE Aig where
  le := Monotone

@[simp ←, grind =_]
theorem mono_eq_le {old new : Aig} :
    old ≤ new ↔ old.Monotone new := by
  rfl

instance : Std.IsPreorder Aig := by
  apply Std.IsPreorder.of_le
  <;> constructor
  · intros; constructor <;> simp
  · simp only [mono_eq_le]; intros; constructor <;> grind only [Monotone]

/-
Theorems for the properties maintained by monotonicity.
-/
section Monotone
variable {old new : Aig} (mono : old ≤ new)
include mono

@[simp, grind .]
theorem var_validIn_mono {var : Var} (valid : var.validIn old) :
    var.validIn new :=
  mono.varValid valid

@[simp, grind .]
theorem input_validIn_mono {idx : InputIdx} (valid : idx.validIn old) :
    idx.validIn new :=
  mono.inputValid valid

@[simp, grind .]
theorem latch_validIn_mono {idx : LatchIdx} (valid : idx.validIn old) :
    idx.validIn new :=
  mono.latchValid valid

@[simp]
theorem get_mono {var : Var} (valid : var.validIn old) :
    new.get var = old.get var :=
  mono.get valid

grind_pattern get_mono => new.get var _, old ≤ new

@[simp]
theorem input_getVar_mono {idx : InputIdx} (valid : idx.validIn old) :
    idx.getVar new = idx.getVar old :=
  mono.inputGetVar valid

grind_pattern input_getVar_mono => idx.getVar new, old ≤ new

@[simp]
theorem latch_getVar_mono {idx : LatchIdx} (valid : idx.validIn old) :
    idx.getVar new = idx.getVar old :=
  mono.latchGetVar valid

grind_pattern latch_getVar_mono => idx.getVar new, old ≤ new

@[simp]
theorem getNext_mono {idx : LatchIdx} (valid : idx.validIn old) :
    idx.getNext new = idx.getNext old :=
  mono.getNext valid

grind_pattern getNext_mono => idx.getNext new, old ≤ new

@[simp]
theorem getReset_mono {idx : LatchIdx} (valid : idx.validIn old) :
    idx.getReset new = idx.getReset old :=
  mono.getReset valid

grind_pattern getReset_mono => idx.getReset new, old ≤ new

end Monotone

section modifiers
variable {aig : Aig}
attribute [local simp] Var.validIn InputIdx.validIn LatchIdx.validIn

@[simp]
theorem mono_addInput :
    aig ≤ aig.addInput.fst := by
  constructor <;> simp_defs <;> grind_defs

grind_pattern mono_addInput => aig.addInput.fst

@[simp]
theorem mono_addLatch {next reset : Lit} :
    aig ≤ (aig.addLatch next reset).fst := by
  constructor <;> simp_defs <;> grind_defs

grind_pattern mono_addLatch => (aig.addLatch next reset).fst

@[simp]
theorem mono_addAnd {rhs0 rhs1 : Lit} (h0 : rhs0.validIn aig) (h1 : rhs1.validIn aig) :
    aig ≤ (aig.addAnd rhs0 rhs1 h0 h1).fst := by
  constructor <;> simp_defs <;> grind_defs

grind_pattern mono_addAnd => (aig.addAnd rhs0 rhs1 h0 h1).fst

end modifiers
