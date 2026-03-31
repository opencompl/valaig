module

import all Valaig.Aig.Basic
public import Valaig.Aig.WellFormed
import all Std.Sat.AIG.Basic
public import Std.Sat.AIG.CachedGatesLemmas

public section
namespace Valaig.Aig

variable {aig : Aig}

/--
An timeframe (step) index of the model.
-/
abbrev Frame := Nat

/--
Combinational (uninitialised) denotation of literals.
-/
@[expose]
def denoteC (aig : Aig) (lit : Lit) (assign : LeafIdx -> Frame -> Bool) (frame : Frame := 0)
    (wf : aig.WellFormed := by grind) :=
  lit.inverted ^^
    match _ : aig[lit.var]? with
    | none
    | some .false           => false
    | some (.input idx)     => assign idx frame
    | some (.latch idx)     =>
      match frame with
      | 0                   => assign idx 0
      | n + 1               => aig.denoteC (idx.getNext aig) assign n
    | some (.and rhs0 rhs1) => aig.denoteC rhs0 assign frame && aig.denoteC rhs1 assign frame
termination_by (frame, lit.var)
decreasing_by all_goals grind

@[expose]
def denoteC.assignNext (aig : Aig) (frame : Frame) (assign : LeafIdx -> Frame -> Bool)
    (wf : aig.WellFormed := by grind) : LeafIdx -> Frame -> Bool :=
  fun idx _ =>
    match _ : decide (idx.validIn aig), _ : idx, _ : frame with
    | true, .latch idx, n + 1 => aig.denoteC (idx.getNext aig) assign n
    |    _,          _,     _ => assign idx frame

/--
Combinational (uninitialised) denotation of variables.
-/
@[expose]
def denoteCV (aig : Aig) (var : Var) (assign : LeafIdx -> Frame -> Bool) (frame : Frame := 0)
    (wf : aig.WellFormed := by grind) :=
  aig.denoteC var.toLit assign frame wf

/--
Sequential (initialised) denotation of literals.
-/
@[expose]
def denoteS (aig : Aig) (lit : Lit) (assign : LeafIdx -> Frame -> Bool) (frame : Frame := 0)
    (wf : aig.WellFormed := by grind) :=
  lit.inverted ^^
    match _ : aig[lit.var]? with
    | none
    | some .false           => false
    | some (.input idx)     => assign idx frame
    | some (.latch idx)     =>
      match frame with
      | 0                   =>
        match _ : idx.getReset aig with
        | none              => assign idx 0
        | some reset        => aig.denoteS reset assign 0
      | n + 1               => aig.denoteS (idx.getNext aig) assign n
    | some (.and rhs0 rhs1) => aig.denoteS rhs0 assign frame && aig.denoteS rhs1 assign frame
termination_by (frame, lit.var)
decreasing_by all_goals grind

@[expose]
def denoteS.assignNext (aig : Aig) (frame : Frame) (assign : LeafIdx -> Frame -> Bool)
    (wf : aig.WellFormed := by grind) : LeafIdx -> Frame -> Bool :=
  fun idx _ =>
    match _ : decide (idx.validIn aig), _ : idx, _ : frame with
    | true, .latch idx, 0     =>
      match idx.getReset aig with
      | none                  => assign idx 0
      | some reset            => aig.denoteS reset assign 0
    | true, .latch idx, n + 1 => aig.denoteS (idx.getNext aig) assign n
    |    _,          _,     _ => assign idx frame

/--
Sequential (initialised) denotation of variables.
-/
@[expose]
def denoteSV (aig : Aig) (var : Var) (assign : LeafIdx -> Frame -> Bool) (frame : Frame := 0)
    (wf : aig.WellFormed := by grind) :=
  aig.denoteS var.toLit assign frame wf

scoped syntax "⟦" term ", " term ", " term (", " term)? ("⟧c" <|> "⟧cv" <|> "⟧s" <|> "⟧sv") (num)? : term

scoped macro_rules
| `(⟦$aig, $lit,         $assign⟧c$frame)  => `(denoteC  $aig $lit $assign $frame)
| `(⟦$aig, $var,         $assign⟧cv$frame) => `(denoteCV $aig $var $assign $frame)
| `(⟦$aig, $lit,         $assign⟧s$frame)  => `(denoteS  $aig $lit $assign $frame)
| `(⟦$aig, $var,         $assign⟧sv$frame) => `(denoteSV $aig $var $assign $frame)
| `(⟦$aig, $lit, $frame, $assign⟧c)        => `(denoteC  $aig $lit $assign $frame)
| `(⟦$aig, $var, $frame, $assign⟧cv)       => `(denoteCV $aig $var $assign $frame)
| `(⟦$aig, $lit, $frame, $assign⟧s)        => `(denoteS  $aig $lit $assign $frame)
| `(⟦$aig, $var, $frame, $assign⟧sv)       => `(denoteSV $aig $var $assign $frame)

@[app_unexpander Aig.denoteC]
meta def unexpandDenoteC : Lean.PrettyPrinter.Unexpander
  | `($(_) $aig $lit $assign      0 $_) => `(⟦$aig, $lit, $assign⟧c0)
  | `($(_) $aig $lit $assign      1 $_) => `(⟦$aig, $lit, $assign⟧c1)
  | `($(_) $aig $lit $assign $frame $_) => `(⟦$aig, $lit, $frame, $assign⟧c)
  | _ => throw ()

@[app_unexpander Aig.denoteCV]
meta def unexpandDenoteCV : Lean.PrettyPrinter.Unexpander
  | `($(_) $aig $var $assign      0 $_) => `(⟦$aig, $var, $assign⟧cv0)
  | `($(_) $aig $var $assign      1 $_) => `(⟦$aig, $var, $assign⟧cv1)
  | `($(_) $aig $var $assign $frame $_) => `(⟦$aig, $var, $frame, $assign⟧cv)
  | _ => throw ()

@[app_unexpander Aig.denoteS]
meta def unexpandDenoteS : Lean.PrettyPrinter.Unexpander
  | `($(_) $aig $lit $assign      0 $_) => `(⟦$aig, $lit, $assign⟧s0)
  | `($(_) $aig $lit $assign      1 $_) => `(⟦$aig, $lit, $assign⟧s1)
  | `($(_) $aig $lit $assign $frame $_) => `(⟦$aig, $lit, $frame, $assign⟧s)
  | _ => throw ()

@[app_unexpander Aig.denoteSV]
meta def unexpandDenoteSV : Lean.PrettyPrinter.Unexpander
  | `($(_) $aig $var $assign      0 $_) => `(⟦$aig, $var, $assign⟧sv0)
  | `($(_) $aig $var $assign      1 $_) => `(⟦$aig, $var, $assign⟧sv1)
  | `($(_) $aig $var $assign $frame $_) => `(⟦$aig, $var, $frame, $assign⟧sv)
  | _ => throw ()

variable {wf : aig.WellFormed} {assign : LeafIdx -> Frame -> Bool} {frame : Frame} {lit : Lit} {var : Var}

/-
Locally we provide extra syntax that automatically assumes it is working within aig/frame to
keep definitions simpler to read.
-/
local syntax "⟦" term (", " term)? ("⟧c" <|> "⟧cv" <|> "⟧s" <|> "⟧sv") (num)? : term
local macro_rules
| `(⟦$lit⟧c)          => `(denoteC  aig $lit assign frame  wf)
| `(⟦$lit⟧cv)         => `(denoteCV aig $lit assign frame  wf)
| `(⟦$lit⟧s)          => `(denoteS  aig $lit assign frame  wf)
| `(⟦$lit⟧sv)         => `(denoteSV aig $lit assign frame  wf)
| `(⟦$lit⟧c$frame)    => `(denoteC  aig $lit assign $frame wf)
| `(⟦$lit⟧cv$frame)   => `(denoteCV aig $lit assign $frame wf)
| `(⟦$lit⟧s$frame)    => `(denoteS  aig $lit assign $frame wf)
| `(⟦$lit⟧sv$frame)   => `(denoteSV aig $lit assign $frame wf)
| `(⟦$lit, $frame⟧c)  => `(denoteC  aig $lit assign $frame wf)
| `(⟦$lit, $frame⟧cv) => `(denoteCV aig $lit assign $frame wf)
| `(⟦$lit, $frame⟧s)  => `(denoteS  aig $lit assign $frame wf)
| `(⟦$lit, $frame⟧sv) => `(denoteSV aig $lit assign $frame wf)

theorem denoteC_zero_eq_assign_zero :
    ⟦lit⟧c0 = ⟦aig, lit, fun idx _ => assign idx 0⟧c0 := by
  induction h : lit.var using WellFounded.induction generalizing lit
  exact WellFoundedRelation.wf
  next ih =>
    simp only [WellFoundedRelation.rel] at ih
    unfold denoteC
    unfold denoteC.assignNext at *
    split <;> grind

theorem denoteS_zero_eq_assign_zero :
    ⟦lit⟧s0 =
    ⟦aig, lit, fun idx _ => assign idx 0⟧s0 := by
  induction h : lit.var using WellFounded.induction generalizing lit
  exact WellFoundedRelation.wf
  next ih =>
    simp only [WellFoundedRelation.rel] at ih
    unfold denoteS
    unfold denoteS.assignNext at *
    split <;> grind

theorem denoteCV_zero_eq_assign_zero :
    ⟦var⟧cv0 = ⟦aig, var, fun idx _ => assign idx 0⟧cv0 := by
  grind [denoteCV, denoteC_zero_eq_assign_zero]

theorem denoteSV_zero_eq_assign_zero :
    ⟦var⟧sv0 = ⟦aig, var, fun idx _ => assign idx 0⟧sv0 := by
  grind [denoteSV, denoteS_zero_eq_assign_zero]

theorem denoteC_eq_denoteC_assignNext :
    ⟦lit⟧c = ⟦aig, lit, denoteC.assignNext aig frame assign⟧c0 := by
  induction h : lit.var using WellFounded.induction generalizing lit
  exact WellFoundedRelation.wf
  next ih =>
    simp only [WellFoundedRelation.rel] at ih
    unfold denoteC
    unfold denoteC.assignNext at *
    split <;> grind

theorem denoteS_eq_denoteC_assignNext :
    ⟦lit⟧s = ⟦aig, lit, denoteS.assignNext aig frame assign⟧c0 := by
  induction h : lit.var using WellFounded.induction generalizing lit
  exact WellFoundedRelation.wf
  next ih =>
    simp only [WellFoundedRelation.rel] at ih
    unfold denoteS denoteC
    unfold denoteS.assignNext at *
    split <;> grind

theorem denoteCV_eq_denoteCV_assignNext :
    ⟦var⟧cv = ⟦aig, var, denoteC.assignNext aig frame assign⟧cv0 := by
  grind [denoteCV, denoteC_eq_denoteC_assignNext]

theorem denoteSV_eq_denoteCV_assignNext :
    ⟦var⟧sv = ⟦aig, var, denoteS.assignNext aig frame assign⟧cv0 := by
  rw [denoteSV, denoteS_eq_denoteC_assignNext, denoteCV]

@[simp, grind =]
theorem denoteC_assignNext_zero {idx : LeafIdx} {f : Frame} :
    (denoteC.assignNext aig 0 assign wf) idx f = assign idx 0 := by
  unfold denoteC.assignNext
  split <;> grind

@[local grind =] theorem denoteC_eq : ⟦lit⟧c = (lit.inverted ^^ ⟦lit.var⟧cv) := by grind [denoteC, denoteCV]
@[local grind =] theorem denoteS_eq : ⟦lit⟧s = (lit.inverted ^^ ⟦lit.var⟧sv) := by grind [denoteS, denoteSV]
grind_pattern denoteC_eq => ⟦aig, lit, frame, assign⟧c, lit.var
grind_pattern denoteS_eq => ⟦aig, lit, frame, assign⟧s, lit.var

theorem denoteCV_eq : ⟦var⟧cv = ⟦var.toLit⟧c := by grind [denoteCV]
theorem denoteSV_eq : ⟦var⟧sv = ⟦var.toLit⟧s := by grind [denoteSV]

@[simp] theorem denoteC_false : ⟦.false⟧c = .false := by grind [denoteC]
@[simp] theorem denoteS_false : ⟦.false⟧s = .false := by grind [denoteS]
@[simp] theorem denoteC_true : ⟦.true⟧c = .true := by grind [denoteC]
@[simp] theorem denoteS_true : ⟦.true⟧s = .true := by grind [denoteS]
@[simp] theorem denoteC_constant {value : Bool} : ⟦.constant value⟧c = value := by grind [denoteC]
@[simp] theorem denoteS_constant {value : Bool} : ⟦.constant value⟧s = value := by grind [denoteS]
@[simp, grind =] theorem denoteCV_constant : ⟦.constant⟧cv = .false := by grind [denoteCV_eq, denoteC]
@[simp, grind =] theorem denoteSV_constant : ⟦.constant⟧sv = .false := by grind [denoteSV_eq, denoteS]

@[simp] theorem denoteC_not_inverted  (h : ¬lit.inverted) : ⟦lit    ⟧c  =  ⟦lit.var⟧cv := by grind
@[simp] theorem denoteS_not_inverted  (h : ¬lit.inverted) : ⟦lit    ⟧s  =  ⟦lit.var⟧sv := by grind
@[simp] theorem denoteC_inverted      (h :  lit.inverted) : ⟦lit    ⟧c  = !⟦lit.var⟧cv := by grind
@[simp] theorem denoteS_inverted      (h :  lit.inverted) : ⟦lit    ⟧s  = !⟦lit.var⟧sv := by grind
@[simp] theorem denoteCV_not_inverted (h : ¬lit.inverted) : ⟦lit.var⟧cv =  ⟦lit    ⟧c := by grind
@[simp] theorem denoteSV_not_inverted (h : ¬lit.inverted) : ⟦lit.var⟧sv =  ⟦lit    ⟧s := by grind
@[simp] theorem denoteCV_inverted     (h :  lit.inverted) : ⟦lit.var⟧cv = !⟦lit    ⟧c := by grind
@[simp] theorem denoteSV_inverted     (h :  lit.inverted) : ⟦lit.var⟧sv = !⟦lit    ⟧s := by grind

@[simp] theorem denoteCV_var_eq : ⟦lit.var⟧cv = (lit.inverted ^^ ⟦lit⟧c) := by grind
@[simp] theorem denoteSV_var_eq : ⟦lit.var⟧sv = (lit.inverted ^^ ⟦lit⟧s) := by grind
grind_pattern denoteCV_var_eq => ⟦aig, lit.var, frame, assign⟧cv where lit =/= Lit.mk _ _
grind_pattern denoteSV_var_eq => ⟦aig, lit.var, frame, assign⟧sv where lit =/= Lit.mk _ _

@[simp, grind =] theorem denoteC_mk {var : Var} {invert : Bool} : ⟦.mk var invert⟧c = (invert ^^ ⟦var⟧cv) := by grind
@[simp, grind =] theorem denoteS_mk {var : Var} {invert : Bool} : ⟦.mk var invert⟧s = (invert ^^ ⟦var⟧sv) := by grind

@[simp] theorem denoteC_invalid  (invalid : ¬lit.validIn aig) : ⟦lit⟧c  = decide lit.inverted := by grind [denoteC]
@[simp] theorem denoteS_invalid  (invalid : ¬lit.validIn aig) : ⟦lit⟧s  = decide lit.inverted := by grind [denoteS]
@[simp] theorem denoteCV_invalid (invalid : ¬var.validIn aig) : ⟦var⟧cv = false               := by grind [denoteCV_eq, denoteC_invalid]
@[simp] theorem denoteSV_invalid (invalid : ¬var.validIn aig) : ⟦var⟧sv = false               := by grind [denoteSV_eq, denoteS_invalid]
grind_pattern denoteC_invalid  => ⟦aig, lit, frame, assign⟧c, lit.validIn aig
grind_pattern denoteS_invalid  => ⟦aig, lit, frame, assign⟧s, lit.validIn aig
grind_pattern denoteCV_invalid => ⟦aig, var, frame, assign⟧cv, var.validIn aig
grind_pattern denoteSV_invalid => ⟦aig, var, frame, assign⟧sv, var.validIn aig

section get
variable {valid : var.validIn aig}

@[simp] theorem denoteCV_get_false (h : aig.get var valid = .false) : ⟦var⟧cv = false := by grind [denoteCV_eq, denoteC]
@[simp] theorem denoteSV_get_false (h : aig.get var valid = .false) : ⟦var⟧sv = false := by grind [denoteSV_eq, denoteS]
grind_pattern denoteCV_get_false => aig.get var, Node.false, ⟦aig, var, frame, assign⟧cv
grind_pattern denoteSV_get_false => aig.get var, Node.false, ⟦aig, var, frame, assign⟧sv

@[simp] theorem denoteCV_get_input {idx : InputIdx} (h : aig.get var valid = .input idx) : ⟦var⟧cv = assign idx frame := by grind [denoteCV_eq, denoteC]
@[simp] theorem denoteSV_get_input {idx : InputIdx} (h : aig.get var valid = .input idx) : ⟦var⟧sv = assign idx frame := by grind [denoteSV_eq, denoteS]
grind_pattern denoteCV_get_input => aig.get var, Node.input idx, ⟦aig, var, frame, assign⟧cv where idx =/= (_ : Aig).addInput.snd
grind_pattern denoteSV_get_input => aig.get var, Node.input idx, ⟦aig, var, frame, assign⟧sv where idx =/= (_ : Aig).addInput.snd

@[simp, grind =] theorem denoteCV_input_getVar {idx : InputIdx} (valid : idx.validIn aig) : ⟦idx.getVar aig valid⟧cv = assign idx frame := by grind [denoteCV_get_input]
@[simp, grind =] theorem denoteSV_input_getVar {idx : InputIdx} (valid : idx.validIn aig) : ⟦idx.getVar aig valid⟧sv = assign idx frame := by grind [denoteSV_get_input]

@[simp]
theorem denoteCV_get_latch_zero {idx : LatchIdx} (h : aig.get var valid = .latch idx) :
    ⟦var⟧cv0 = assign idx 0 := by
  grind [denoteCV_eq, denoteC]

grind_pattern denoteCV_get_latch_zero => aig.get var, Node.latch idx, ⟦aig, var, 0, assign⟧cv where
  idx =/= ((_ : Aig).addLatch _ _).snd

@[simp]
theorem denoteSV_get_latch_zero {idx : LatchIdx} (h : aig.get var valid = .latch idx) :
    ⟦var⟧sv0 =
    match idx.getReset aig with
    | none       => assign idx 0
    | some reset => ⟦reset⟧s0 := by
  grind [denoteSV_eq, denoteS]

grind_pattern denoteSV_get_latch_zero => aig.get var, Node.latch idx, ⟦aig, var, 0, assign⟧sv where
  idx =/= ((_ : Aig).addLatch _ _).snd

@[simp]
theorem denoteCV_get_latch {idx : LatchIdx} (h : aig.get var valid = .latch idx) :
    ⟦var⟧cv =
    match frame with
    | 0     => assign idx 0
    | n + 1 => ⟦idx.getNext aig, n⟧c := by
  grind [denoteCV, denoteC]

grind_pattern denoteCV_get_latch => aig.get var, Node.latch idx, ⟦aig, var, frame, assign⟧cv where
  idx =/= ((_ : Aig).addLatch _ _).snd
  frame =/= 0

@[simp]
theorem denoteSV_get_latch {idx : LatchIdx} (h : aig.get var valid = .latch idx) :
    ⟦var⟧sv =
    match frame with
    | 0            =>
      match idx.getReset aig with
      | none       => assign idx 0
      | some reset => ⟦reset⟧s0
    | n + 1        => ⟦idx.getNext aig, n⟧s := by
  grind [denoteSV, denoteS]

grind_pattern denoteSV_get_latch => aig.get var, Node.latch idx, ⟦aig, var, frame, assign⟧sv where
  idx =/= ((_ : Aig).addLatch _ _).snd
  frame =/= 0

@[simp, grind =]
theorem denoteCV_latch_getVar_zero {idx : LatchIdx} (valid : idx.validIn aig) :
    ⟦idx.getVar aig valid⟧cv0 = assign idx 0 := by
  grind [get_latch_getVar]

@[simp, grind =]
theorem denoteSV_latch_getVar_zero {idx : LatchIdx} (valid : idx.validIn aig) :
    ⟦idx.getVar aig valid⟧sv0 =
    match idx.getReset aig with
    | none       => assign idx 0
    | some reset => ⟦reset⟧s0 := by
  grind [get_latch_getVar]

@[simp]
theorem denoteCV_latch_getVar {idx : LatchIdx} (valid : idx.validIn aig) :
    ⟦idx.getVar aig valid⟧cv =
    match frame with
    | 0     => assign idx 0
    | n + 1 => ⟦idx.getNext aig, n⟧c := by
  grind [get_latch_getVar, denoteCV_get_latch]

grind_pattern denoteCV_latch_getVar => ⟦aig, idx.getVar aig, frame, assign⟧cv where
  frame =/= 0

@[simp]
theorem denoteSV_latch_getVar {idx : LatchIdx} (valid : idx.validIn aig) :
    ⟦idx.getVar aig valid⟧sv =
    match frame with
    | 0            =>
      match idx.getReset aig with
      | none       => assign idx 0
      | some reset => ⟦reset⟧s0
    | n + 1        => ⟦idx.getNext aig, n⟧s := by
  grind [get_latch_getVar, denoteCV_get_latch]

grind_pattern denoteSV_latch_getVar => ⟦aig, idx.getVar aig, frame, assign⟧sv where
  frame =/= 0

@[simp] theorem denoteCV_get_and {rhs0 rhs1 : Lit} (h : aig.get var valid = .and rhs0 rhs1) : ⟦var⟧cv = (⟦rhs0⟧c && ⟦rhs1⟧c) := by grind [denoteCV, denoteC]
@[simp] theorem denoteSV_get_and {rhs0 rhs1 : Lit} (h : aig.get var valid = .and rhs0 rhs1) : ⟦var⟧sv = (⟦rhs0⟧s && ⟦rhs1⟧s) := by grind [denoteSV, denoteS]
grind_pattern denoteCV_get_and => aig.get var, Node.and rhs0 rhs1, ⟦aig, var, frame, assign⟧cv
grind_pattern denoteSV_get_and => aig.get var, Node.and rhs0 rhs1, ⟦aig, var, frame, assign⟧sv

end get

section mono
variable {old new : Aig} {oldWf : old.WellFormed} {newWf : new.WellFormed} (mono : old ≤ new)
include mono

theorem denoteC_mono (valid : lit.validIn old) :
    ⟦new, lit, frame, assign⟧c = ⟦old, lit, frame, assign⟧c := by
  induction _ : (frame, lit.var) using WellFounded.induction generalizing lit frame
  exact WellFoundedRelation.wf
  next ih _ =>
    simp only [WellFoundedRelation.rel, Prod.lex_def, InvImage, sizeOf_nat] at ih
    unfold denoteC
    grind

grind_pattern denoteC_mono => ⟦new, lit, frame, assign⟧c, old ≤ new

theorem denoteS_mono (valid : lit.validIn old) :
    ⟦new, lit, frame, assign⟧s = ⟦old, lit, frame, assign⟧s := by
  induction _ : (frame, lit.var) using WellFounded.induction generalizing lit frame
  exact WellFoundedRelation.wf
  next ih _ =>
    simp only [WellFoundedRelation.rel, Prod.lex_def, InvImage, sizeOf_nat] at ih
    unfold denoteS
    grind

grind_pattern denoteS_mono => ⟦new, lit, frame, assign⟧s, old ≤ new

theorem denoteCV_mono (valid : var.validIn old) : ⟦new, var, frame, assign⟧cv = ⟦old, var, frame, assign⟧cv := by grind [denoteC_mono, denoteCV_eq]
theorem denoteSV_mono (valid : var.validIn old) : ⟦new, var, frame, assign⟧sv = ⟦old, var, frame, assign⟧sv := by grind [denoteS_mono, denoteSV_eq]
grind_pattern denoteCV_mono => ⟦new, var, frame, assign⟧cv, old ≤ new
grind_pattern denoteSV_mono => ⟦new, var, frame, assign⟧sv, old ≤ new

end mono

open Std.Sat AIG in
private theorem denoteC_eq_std_denote :
    ⟦lit⟧c0 =
    if valid : lit.validIn aig then
      AIG.denote (assign · 0) (Entrypoint.mk aig.aig <| lit.toRef valid)
    else
      lit.inverted := by
  induction h : lit.var using WellFounded.induction generalizing lit
  exact WellFoundedRelation.wf
  next ih =>
    simp only [WellFoundedRelation.rel] at ih
    unfold AIG.denote AIG.denote.go
    split
    case isTrue valid =>
      cases h : aig[lit.var] with
      | false     => clear ih; grind [get_eq_getElem_decls_false valid h]
      | input idx => clear ih; grind [get_eq_getElem_decls_input valid h]
      | latch idx => clear ih; grind [get_eq_getElem_decls_latch valid h]
      | and rhs0 rhs1 =>
        rw [denoteC_eq, denoteCV_get_and h, ih rhs0.var, ih rhs1.var]
        · unfold AIG.denote
          grind [get_eq_getElem_decls_and valid h]
        all_goals (clear ih; grind)
    case isFalse => grind

section addInput'
variable {idx : InputIdx} {wf : (aig.addInput' idx).WellFormed}

@[simp, grind =] theorem denoteCV_addInput'_self : ⟦aig.addInput' idx, idx.getVar (aig.addInput' idx), frame, assign⟧cv = assign idx frame := by grind
@[simp, grind =] theorem denoteSV_addInput'_self : ⟦aig.addInput' idx, idx.getVar (aig.addInput' idx), frame, assign⟧sv = assign idx frame := by grind

end addInput'

section addLatch
variable {idx : LatchIdx} {next : Lit} {reset : Option Lit}
variable (wf : (aig.addLatch' idx next reset).WellFormed)

@[simp, grind =]
theorem denoteCV_addLatch'_self_zero :
    ⟦aig.addLatch' idx next reset, idx.getVar (aig.addLatch' idx next reset), assign⟧cv0 =
    assign idx 0 := by
  grind

@[simp]
theorem denoteSV_addLatch'_self_zero_none (wf : (aig.addLatch' idx next none).WellFormed) :
    ⟦aig.addLatch' idx next none, idx.getVar (aig.addLatch' idx next none), assign⟧sv0 =
    assign idx 0 := by
  grind

@[simp]
theorem denoteSV_addLatch'_self_zero_some {reset : Lit}
    (wf : (aig.addLatch' idx next <| some reset).WellFormed)
    (resetValid : reset.validIn aig)
    (h : ¬idx.validIn aig) :
    ⟦aig.addLatch' idx next <| some reset, idx.getVar (aig.addLatch' idx next <| some reset), assign⟧sv0 =
    ⟦reset⟧s0 := by
  grind

@[simp, grind =]
theorem denoteSV_addLatch'_self_zero
    (wf : (aig.addLatch' idx next reset).WellFormed)
    (resetValid :
      match reset with
      | none => True
      | some reset => reset.validIn aig)
    (h : ¬idx.validIn aig) :
    ⟦aig.addLatch' idx next reset, idx.getVar (aig.addLatch' idx next reset), assign⟧sv0 =
    match reset with
    | none       => assign idx 0
    | some reset => ⟦reset⟧s0 := by
  grind

@[simp, grind =]
theorem denoteCV_addLatch'_self {idx : LatchIdx} {next : Lit} {reset : Option Lit}
    (wf : (aig.addLatch' idx next reset).WellFormed)
    (nextValid : next.validIn aig)
    (h : ¬idx.validIn aig) :
    ⟦aig.addLatch' idx next reset, idx.getVar (aig.addLatch' idx next reset), frame, assign⟧cv =
    match frame with
    | 0     => assign idx 0
    | n + 1 => ⟦next, n⟧c := by
  grind

grind_pattern denoteCV_addLatch'_self => ⟦aig.addLatch' idx next reset, idx.getVar (aig.addLatch' idx next reset), frame, assign⟧cv where
  frame =/= 0

@[simp, grind =]
theorem denoteSV_addLatch'_self
    (wf : (aig.addLatch' idx next reset).WellFormed)
    (resetValid :
      match reset with
      | none => True
      | some reset => reset.validIn aig)
    (nextValid : next.validIn aig)
    (h : ¬idx.validIn aig) :
    ⟦aig.addLatch' idx next reset, idx.getVar (aig.addLatch' idx next reset), frame, assign⟧sv =
    match frame with
    | 0            =>
      match reset with
      | none       => assign idx 0
      | some reset => ⟦reset⟧s0
    | n + 1        => ⟦next, n⟧s := by
  grind

grind_pattern denoteSV_addLatch'_self => ⟦aig.addLatch' idx next reset, idx.getVar (aig.addLatch' idx next reset), frame, assign⟧sv where
  frame =/= 0

end addLatch

section addAnd
variable {rhs0 rhs1 : Lit} (h0 : rhs0.validIn aig) (h1 : rhs1.validIn aig)

@[simp]
theorem denoteC_addAnd_self :
    let res := aig.addAnd rhs0 rhs1 h0 h1
    ⟦res.fst, res.snd, frame, assign⟧c = (⟦rhs0⟧c && ⟦rhs1⟧c) := by
  intro res
  suffices h : ∀ (assign), ⟦res.fst, res.snd, assign⟧c0 = (⟦aig, rhs0, assign⟧c0 && ⟦aig, rhs1, assign⟧c0) by
    have : denoteC.assignNext res.fst frame assign = denoteC.assignNext aig frame assign := by
      funext _ _
      unfold denoteC.assignNext
      grind
    conv =>
      pattern (occs := *) ⟦_, _, frame, _⟧c
      <;> rw [denoteC_eq_denoteC_assignNext]
    simp only [this, h]
  intro assign
  simp only [res, denoteC_eq_std_denote]
  split
  · simp only [addAnd, Lit.toRef_ofRef]
    rw [Std.Sat.AIG.denote_mkAndCached]
  · grind

grind_pattern denoteC_addAnd_self => ⟦(aig.addAnd rhs0 rhs1 h0 h1).fst, (aig.addAnd rhs0 rhs1 h0 h1).snd, frame, assign⟧c

@[simp]
theorem denoteS_addAnd_self :
    let res := aig.addAnd rhs0 rhs1 h0 h1
    ⟦res.fst, res.snd, frame, assign⟧s = (⟦rhs0⟧s && ⟦rhs1⟧s) := by
  intro res
  have : denoteS.assignNext res.fst frame assign = denoteS.assignNext aig frame assign := by
    funext _ _
    unfold denoteS.assignNext
    grind
  simp only [denoteS_eq_denoteC_assignNext]
  grind

grind_pattern denoteS_addAnd_self => ⟦(aig.addAnd rhs0 rhs1 h0 h1).fst, (aig.addAnd rhs0 rhs1 h0 h1).snd, frame, assign⟧s

end addAnd

/--
A literal is unsatisfiable in an Aig if for all assignments to inputs and latches its value is
false.
-/
def Unsat (aig : Aig) (lit : Lit) (wf : aig.WellFormed := by grind) : Prop :=
  ∀ {assign},
    ⟦aig, lit, assign⟧c0 = false

theorem Unsat_iff :
    aig.Unsat lit ↔
    (∀ (assign : LeafIdx -> Bool), ⟦aig, lit, fun idx _ => assign idx⟧c0 = false) := by
  unfold Unsat
  constructor
  · grind
  · intro h assign
    rw [denoteC_zero_eq_assign_zero]
    grind [h (fun idx => assign idx 0)]

open Std.Sat AIG in
private theorem Unsat_iff_std_Unsat (valid : lit.validIn aig) :
    aig.Unsat lit wf ↔
    Entrypoint.Unsat (.mk aig.aig <| lit.toRef valid) := by
  rw [Unsat_iff]
  · simp only [AIG.Entrypoint.Unsat, AIG.UnsatAt, denoteC_eq_std_denote, valid]
    grind
  · grind

/--
A literal is unreachable if there is no trace that can reach a state where it is true.
-/
@[expose]
def Unreachable (aig : Aig) (lit : Lit) (wf : aig.WellFormed := by grind) :=
  ∀ {frame assign},
    ⟦aig, lit, frame, assign⟧s = false
