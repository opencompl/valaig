module

public import Valaig.Aig.Core

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
    (wf : aig.WF := by grind) : Bool :=
  match _ : aig[lit.var]? with
  | none
  | some .false           => lit.inverted
  | some (.input idx)     => lit.inverted ^^ assign idx frame
  | some (.latch idx)     =>
    match _ : frame with
    | 0                   => lit.inverted ^^ assign idx 0
    | n + 1               => lit.inverted ^^ aig.denoteC (idx.getNext aig) assign n
  | some (.and rhs0 rhs1) => lit.inverted ^^ (aig.denoteC rhs0 assign frame && aig.denoteC rhs1 assign frame)
termination_by (frame, lit.var)
decreasing_by all_goals grind

@[expose]
def denoteC.assignNext (aig : Aig) (frame : Frame) (assign : LeafIdx -> Frame -> Bool)
    (wf : aig.WF := by grind) : LeafIdx -> Frame -> Bool :=
  fun idx _ =>
    match _ : decide (idx.validIn aig), _ : idx, _ : frame with
    | true, .latch idx, n + 1 => aig.denoteC (idx.getNext aig) assign n
    |    _,          _,     _ => assign idx frame

/--
  Combinational (uninitialised) denotation of variables.
-/
@[expose]
def denoteCV (aig : Aig) (var : Var) (assign : LeafIdx -> Frame -> Bool) (frame : Frame := 0)
    (wf : aig.WF := by grind) : Bool :=
  aig.denoteC var.toLit assign frame wf

/--
  Sequential (initialised) denotation of literals.
-/
@[expose]
def denoteS (aig : Aig) (lit : Lit) (assign : LeafIdx -> Frame -> Bool) (frame : Frame := 0)
    (wf : aig.WF := by grind) : Bool :=
  match _ : aig[lit.var]? with
  | none
  | some .false           => lit.inverted
  | some (.input idx)     => lit.inverted ^^ assign idx frame
  | some (.latch idx)     =>
    match _ : frame with
    | 0                   =>
      match _ : idx.getReset aig with
      | none              => lit.inverted ^^ assign idx 0
      | some reset        => lit.inverted ^^ aig.denoteS reset assign 0
    | n + 1               => lit.inverted ^^ aig.denoteS (idx.getNext aig) assign n
  | some (.and rhs0 rhs1) => lit.inverted ^^ (aig.denoteS rhs0 assign frame && aig.denoteS rhs1 assign frame)
termination_by (frame, lit.var)
decreasing_by all_goals grind

@[expose]
def denoteS.assignNext (aig : Aig) (frame : Frame) (assign : LeafIdx -> Frame -> Bool)
    (wf : aig.WF := by grind) : LeafIdx -> Frame -> Bool :=
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
    (wf : aig.WF := by grind) : Bool :=
  aig.denoteS var.toLit assign frame wf

end Aig

scoped syntax "⟦" term ", " term ", " term (", " term)? ("⟧c" <|> "⟧cv" <|> "⟧s" <|> "⟧sv") (num)? : term

scoped macro_rules
| `(⟦$aig, $lit,         $assign⟧c$frame)  => `(_root_.Valaig.Aig.denoteC  $aig $lit $assign $frame)
| `(⟦$aig, $var,         $assign⟧cv$frame) => `(_root_.Valaig.Aig.denoteCV $aig $var $assign $frame)
| `(⟦$aig, $lit,         $assign⟧s$frame)  => `(_root_.Valaig.Aig.denoteS  $aig $lit $assign $frame)
| `(⟦$aig, $var,         $assign⟧sv$frame) => `(_root_.Valaig.Aig.denoteSV $aig $var $assign $frame)
| `(⟦$aig, $lit, $frame, $assign⟧c)        => `(_root_.Valaig.Aig.denoteC  $aig $lit $assign $frame)
| `(⟦$aig, $var, $frame, $assign⟧cv)       => `(_root_.Valaig.Aig.denoteCV $aig $var $assign $frame)
| `(⟦$aig, $lit, $frame, $assign⟧s)        => `(_root_.Valaig.Aig.denoteS  $aig $lit $assign $frame)
| `(⟦$aig, $var, $frame, $assign⟧sv)       => `(_root_.Valaig.Aig.denoteSV $aig $var $assign $frame)

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

namespace Aig

variable {aig : Aig} {wf : aig.WF} {assign : LeafIdx -> Frame -> Bool} {frame : Frame} {lit : Lit} {var : Var}

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

@[local grind =]
theorem denoteC_eq :
    ⟦lit⟧c = (lit.inverted ^^ ⟦lit.var⟧cv) := by
  grind [denoteC, denoteCV]

grind_pattern denoteC_eq => ⟦aig, lit, frame, assign⟧c, lit.var

@[local grind =]
theorem denoteS_eq :
    ⟦lit⟧s = (lit.inverted ^^ ⟦lit.var⟧sv) := by
  sorry

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
theorem denoteCV_not_inverted (h : ¬lit.inverted) : ⟦lit.var⟧cv =  ⟦lit    ⟧c := by grind
theorem denoteSV_not_inverted (h : ¬lit.inverted) : ⟦lit.var⟧sv =  ⟦lit    ⟧s := by grind
theorem denoteCV_inverted     (h :  lit.inverted) : ⟦lit.var⟧cv = !⟦lit    ⟧c := by grind
theorem denoteSV_inverted     (h :  lit.inverted) : ⟦lit.var⟧sv = !⟦lit    ⟧s := by grind

theorem denoteCV_var_eq : ⟦lit.var⟧cv = (lit.inverted ^^ ⟦lit⟧c) := by grind
theorem denoteSV_var_eq : ⟦lit.var⟧sv = (lit.inverted ^^ ⟦lit⟧s) := by grind
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
variable {mem : var ∈ aig.nodes}

@[simp] theorem denoteCV_getElem_nodes_false (h : aig.nodes[var]'mem = .false) : ⟦var⟧cv = false := by grind [denoteCV_eq, denoteC]
@[simp] theorem denoteSV_getElem_nodes_false (h : aig.nodes[var]'mem = .false) : ⟦var⟧sv = false := by grind [denoteSV_eq, denoteS]
grind_pattern denoteCV_getElem_nodes_false => aig.nodes[var], Node.false, ⟦aig, var, frame, assign⟧cv
grind_pattern denoteSV_getElem_nodes_false => aig.nodes[var], Node.false, ⟦aig, var, frame, assign⟧sv

@[simp] theorem denoteCV_getElem_nodes_input {idx : InputIdx} (h : aig.nodes[var]'mem = .input idx) : ⟦var⟧cv = assign idx frame := by grind [denoteCV_eq, denoteC]
@[simp] theorem denoteSV_getElem_nodes_input {idx : InputIdx} (h : aig.nodes[var]'mem = .input idx) : ⟦var⟧sv = assign idx frame := by grind [denoteSV_eq, denoteS]
grind_pattern denoteCV_getElem_nodes_input => aig.nodes[var], Node.input idx, ⟦aig, var, frame, assign⟧cv where idx =/= (_ : Aig).addInput.snd
grind_pattern denoteSV_getElem_nodes_input => aig.nodes[var], Node.input idx, ⟦aig, var, frame, assign⟧sv where idx =/= (_ : Aig).addInput.snd

@[simp, grind =] theorem denoteCV_var_inputs {idx : InputIdx} (mem : idx ∈ aig.inputs) : ⟦(aig.inputs[idx]'mem).var⟧cv = assign idx frame := by grind [denoteCV_getElem_nodes_input]
@[simp, grind =] theorem denoteSV_var_inputs {idx : InputIdx} (mem : idx ∈ aig.inputs) : ⟦(aig.inputs[idx]'mem).var⟧sv = assign idx frame := by grind [denoteSV_getElem_nodes_input]

@[simp]
theorem denoteCV_getElem_nodes_latch_zero {idx : LatchIdx} (h : aig.nodes[var]'mem = .latch idx) :
    ⟦var⟧cv0 = assign idx 0 := by
  grind [denoteCV_eq, denoteC]

grind_pattern denoteCV_getElem_nodes_latch_zero => aig.nodes[var], Node.latch idx, ⟦aig, var, 0, assign⟧cv where
  idx =/= ((_ : Aig).addLatch _ _).snd

@[simp]
theorem denoteSV_getElem_nodes_latch_zero {idx : LatchIdx} (h : aig.nodes[var]'mem = .latch idx) :
    ⟦var⟧sv0 =
      match idx.getReset aig with
      | none       => assign idx 0
      | some reset => ⟦reset⟧s0 := by
  rw [denoteSV_eq]
  generalize h : 0 = frame
  generalize hvar : var.toLit = var
  fun_induction denoteS aig var assign frame
  · grind
  · grind
  · grind
  · simp only [←hvar, Var.toLit, Lit.inverted_mk, Bool.false_eq_true, decide_false, Bool.false_bne]
    grind
  · grind
  · grind
  · grind

grind_pattern denoteSV_getElem_nodes_latch_zero => aig.nodes[var], Node.latch idx, ⟦aig, var, 0, assign⟧sv where
  idx =/= ((_ : Aig).addLatch _ _).snd

@[simp]
theorem denoteCV_getElem_nodes_latch {idx : LatchIdx} (h : aig.nodes[var]'mem = .latch idx) :
    ⟦var⟧cv =
      match frame with
      | 0     => assign idx 0
      | n + 1 => ⟦idx.getNext aig, n⟧c := by
  grind [denoteCV, denoteC]

grind_pattern denoteCV_getElem_nodes_latch => aig.nodes[var], Node.latch idx, ⟦aig, var, frame, assign⟧cv where
  idx =/= ((_ : Aig).addLatch _ _).snd
  frame =/= 0

@[simp]
theorem denoteSV_getElem_nodes_latch {idx : LatchIdx} (h : aig.nodes[var]'mem = .latch idx) :
    ⟦var⟧sv =
      match frame with
      | 0            =>
        match idx.getReset aig with
        | none       => assign idx 0
        | some reset => ⟦reset⟧s0
      | n + 1        => ⟦idx.getNext aig, n⟧s := by
  rw [denoteSV_eq]
  generalize hvar : var.toLit = var
  fun_induction denoteS aig var assign frame <;> grind

grind_pattern denoteSV_getElem_nodes_latch => aig.nodes[var], Node.latch idx, ⟦aig, var, frame, assign⟧sv where
  idx =/= ((_ : Aig).addLatch _ _).snd
  frame =/= 0

@[simp, grind =]
theorem denoteCV_var_latches_zero {idx : LatchIdx} (mem : idx ∈ aig.latches) :
    ⟦(aig.latches[idx]'mem).var⟧cv0 = assign idx 0 := by
  apply denoteCV_getElem_nodes_latch_zero <;> grind

@[simp, grind =]
theorem denoteSV_var_latches_zero {idx : LatchIdx} (mem : idx ∈ aig.latches) :
    ⟦(aig.latches[idx]'mem).var⟧sv0 =
      match idx.getReset aig with
      | none       => assign idx 0
      | some reset => ⟦reset⟧s0 := by
  apply denoteSV_getElem_nodes_latch_zero <;> grind

@[simp]
theorem denoteCV_var_latches {idx : LatchIdx} (mem : idx ∈ aig.latches) :
    ⟦(aig.latches[idx]'mem).var⟧cv =
      match frame with
      | 0     => assign idx 0
      | n + 1 => ⟦idx.getNext aig, n⟧c := by
  apply denoteCV_getElem_nodes_latch <;> grind

grind_pattern denoteCV_var_latches => ⟦aig, aig.latches[idx].var, frame, assign⟧cv where
  frame =/= 0

@[simp]
theorem denoteSV_var_latches {idx : LatchIdx} (mem : idx ∈ aig.latches) :
    ⟦(aig.latches[idx]'mem).var⟧sv =
    match frame with
    | 0            =>
      match idx.getReset aig with
      | none       => assign idx 0
      | some reset => ⟦reset⟧s0
    | n + 1        => ⟦idx.getNext aig, n⟧s := by
  apply denoteSV_getElem_nodes_latch <;> grind

grind_pattern denoteSV_var_latches => ⟦aig, aig.latches[idx].var, frame, assign⟧sv where
  frame =/= 0

@[simp] theorem denoteCV_getElem_nodes_and {rhs0 rhs1 : Lit} (h : aig.nodes[var]'mem = .and rhs0 rhs1) : ⟦var⟧cv = (⟦rhs0⟧c && ⟦rhs1⟧c) := by grind [denoteCV, denoteC]
@[simp] theorem denoteSV_getElem_nodes_and {rhs0 rhs1 : Lit} (h : aig.nodes[var]'mem = .and rhs0 rhs1) : ⟦var⟧sv = (⟦rhs0⟧s && ⟦rhs1⟧s) := by grind [denoteSV, denoteS]
grind_pattern denoteCV_getElem_nodes_and => aig.nodes[var], Node.and rhs0 rhs1, ⟦aig, var, frame, assign⟧cv
grind_pattern denoteSV_getElem_nodes_and => aig.nodes[var], Node.and rhs0 rhs1, ⟦aig, var, frame, assign⟧sv

end get

theorem denoteC_eq_denoteC_assignNext :
    ⟦lit⟧c = ⟦aig, lit, denoteC.assignNext aig frame assign⟧c0 := by
  unfold denoteC.assignNext
  fun_induction denoteC <;> grind

theorem denoteS_eq_denoteC_assignNext :
    ⟦lit⟧s = ⟦aig, lit, denoteS.assignNext aig frame assign⟧c0 := by
  unfold denoteS.assignNext
  fun_induction denoteS <;> grind

theorem denoteCV_eq_denoteCV_assignNext :
    ⟦var⟧cv = ⟦aig, var, denoteC.assignNext aig frame assign⟧cv0 := by
  grind [denoteCV, denoteC_eq_denoteC_assignNext]

theorem denoteSV_eq_denoteCV_assignNext :
    ⟦var⟧sv = ⟦aig, var, denoteS.assignNext aig frame assign⟧cv0 := by
  rw [denoteSV, denoteS_eq_denoteC_assignNext, denoteCV]

@[simp, grind =]
theorem denoteC_assignNext_zero  :
    (denoteC.assignNext aig 0 assign wf) = fun idx _ => assign idx 0 := by
  unfold denoteC.assignNext
  grind

theorem denoteC_zero_eq_assign_zero :
    ⟦lit⟧c0 = ⟦aig, lit, fun idx _ => assign idx 0⟧c0 := by
  grind [denoteC_eq_denoteC_assignNext]

theorem denoteS_zero_eq_assign_zero :
    ⟦lit⟧s0 = ⟦aig, lit, fun idx _ => assign idx 0⟧s0 := by
  induction h : lit.var using WellFounded.induction generalizing lit
  exact WellFoundedRelation.wf
  next ih =>
    simp only [WellFoundedRelation.rel] at ih
    unfold denoteS
    split <;> grind

theorem denoteCV_zero_eq_assign_zero :
    ⟦var⟧cv0 = ⟦aig, var, fun idx _ => assign idx 0⟧cv0 := by
  grind [denoteCV, denoteC_zero_eq_assign_zero]

theorem denoteSV_zero_eq_assign_zero :
    ⟦var⟧sv0 = ⟦aig, var, fun idx _ => assign idx 0⟧sv0 := by
  grind [denoteSV, denoteS_zero_eq_assign_zero]


section mono
variable {old new : Aig} {oldWf : old.WF} {newWf : new.WF} (mono : old ≤ new)
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
  fun_induction denoteS new lit assign frame <;> grind

grind_pattern denoteS_mono => ⟦new, lit, frame, assign⟧s, old ≤ new

theorem denoteCV_mono (mem : var ∈ old.nodes) : ⟦new, var, frame, assign⟧cv = ⟦old, var, frame, assign⟧cv := by grind [denoteC_mono, denoteCV_eq]
theorem denoteSV_mono (mem : var ∈ old.nodes) : ⟦new, var, frame, assign⟧sv = ⟦old, var, frame, assign⟧sv := by grind [denoteS_mono, denoteSV_eq]
grind_pattern denoteCV_mono => ⟦new, var, frame, assign⟧cv, old ≤ new
grind_pattern denoteSV_mono => ⟦new, var, frame, assign⟧sv, old ≤ new

end mono

section denote_of_assign_eq
variable (assign' : LeafIdx -> Frame -> Bool)

section lit
variable (h : ∀ (idx frame') (valid : idx.validIn aig),
           frame' < frame ∨ (frame' = frame ∧ idx.getVar aig valid ≤ lit.var) →
             assign idx frame' = assign' idx frame')
include h

theorem denoteC_of_assign_eq :
    ⟦aig, lit, frame, assign⟧c = ⟦aig, lit, frame, assign'⟧c := by
  induction _ : (frame, lit.var) using WellFounded.induction generalizing lit frame
  exact WellFoundedRelation.wf
  next ih _ =>
    simp only [WellFoundedRelation.rel, Prod.lex_def, InvImage, sizeOf_nat] at ih
    unfold denoteC
    split
    · clear ih h; grind
    · clear ih h; grind
    · clear ih; grind [h (frame' := frame)]
    · split
      · grind
      · grind
    · grind

theorem denoteS_of_assign_eq :
    ⟦aig, lit, frame, assign⟧s = ⟦aig, lit, frame, assign'⟧s := by
  induction _ : (frame, lit.var) using WellFounded.induction generalizing lit frame
  exact WellFoundedRelation.wf
  next ih _ =>
    simp only [WellFoundedRelation.rel, Prod.lex_def, InvImage, sizeOf_nat] at ih
    unfold denoteS
    split
    · clear ih h; grind
    · clear ih h; grind
    · clear ih; grind [h (frame' := frame)]
    · split
      · grind
      · grind
    · grind

end lit

section var
variable (h : ∀ (idx frame') (valid : idx.validIn aig),
           frame' < frame ∨ (frame' = frame ∧ idx.getVar aig valid ≤ var) →
             assign idx frame' = assign' idx frame')
include h

theorem denoteCV_of_assign_eq :
    ⟦aig, var, frame, assign⟧cv = ⟦aig, var, frame, assign'⟧cv := by
  grind [denoteCV_eq, denoteC_of_assign_eq]

theorem denoteSV_of_assign_eq :
    ⟦aig, var, frame, assign⟧sv = ⟦aig, var, frame, assign'⟧sv := by
  grind [denoteSV_eq, denoteS_of_assign_eq]

end var

end denote_of_assign_eq

/--
  A literal is unsatisfiable in an Aig if for all assignments to inputs and latches its value is
  false.
-/
def Unsat (aig : Aig) (lit : Lit) (wf : aig.WF := by grind) : Prop :=
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

/--
  A literal is unreachable if there is no trace that can reach a state where it is true.
-/
@[expose]
def Unreachable (aig : Aig) (lit : Lit) (wf : aig.WF := by grind) :=
  ∀ {frame assign},
    ⟦aig, lit, frame, assign⟧s = false
