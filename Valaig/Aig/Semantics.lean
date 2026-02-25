module

import all Valaig.Aig.Basic
public import Valaig.Aig.WellFormed
import all Std.Sat.AIG.Basic

public section
namespace Valaig.Aig

variable {aig : Aig}

/--
An timeframe (step) index of the model.
-/
abbrev Frame := Nat

/--
A combinational Aig has no latches.
-/
def Comb (aig : Aig) :=
  aig.numLatches = 0

@[local simp]
theorem Comb_def :
    aig.Comb ↔ aig.numLatches = 0 := by
  rfl

grind_pattern Comb_def => aig.Comb, aig.numLatches

theorem Comb_iff_latch_not_validIn :
    aig.Comb ↔ ∀ {latch : LatchIdx}, ¬latch.validIn aig := by
  simp [Comb_def, numLatches_zero_iff_not_validIn]

@[simp]
theorem latch_not_validIn_of_Comb (comb : aig.Comb) (latch : LatchIdx) :
    ¬latch.validIn aig :=
  Comb_iff_latch_not_validIn.mp comb

grind_pattern latch_not_validIn_of_Comb => aig.Comb, latch.validIn aig

/--
Denotation of the combinational semantics of the Aig, taking a function to assign
values to the inputs and latches.
-/
@[expose]
def denoteComb (aig : Aig) (lit : Lit) (assign : LeafIdx.In aig -> Bool)
    (valid : lit.validIn aig := by grind) (wf : aig.WellFormed := by grind) : Bool :=
  denoteLit lit
where
  denoteLit (lit : Lit) (valid : lit.validIn aig := by grind) :=
    denoteVar lit.var valid ^^ lit.inverted
  termination_by (lit.var, 1)

  denoteVar (var : Var) (valid : var.validIn aig) : Bool :=
    match h : aig[var]'valid with
    | .false         => false
    | .input idx     => assign <| idx.castIn aig
    | .latch idx     => assign <| idx.castIn aig
    | .and rhs0 rhs1 => denoteLit rhs0 && denoteLit rhs1
  termination_by (var, 0)
  decreasing_by all_goals grind

/--
Denotation of the sequential semantics of the Aig in each timeframe, taking a function to assign
values to the inputs in each frame.
-/
@[expose]
def denoteSeq (aig : Aig) (lit : Lit) (frame : Frame) (assign : InputIdx.In aig -> Frame -> Bool)
    (valid : lit.validIn aig := by grind) (wf : aig.WellFormed := by grind) : Bool :=
  denoteLit lit frame
where
  denoteLit (lit : Lit) (frame : Frame) (valid : lit.validIn aig := by grind) :=
    denoteVar lit.var frame valid ^^ lit.inverted
  termination_by (frame, lit.var, 1)

  denoteVar (var : Var) (frame : Frame) (valid : var.validIn aig) : Bool :=
    match _ : aig[var]'valid, _ : frame with
    | .false, _         => false
    | .input idx, _     => assign (idx.castIn aig) frame
    | .latch idx, 0     => denoteLit (idx.getReset aig) 0
    | .latch idx, n + 1 => denoteLit (idx.getNext aig) n
    | .and rhs0 rhs1, _ => denoteLit rhs0 frame && denoteLit rhs1 frame
  termination_by (frame, var, 0)
  decreasing_by all_goals grind [wfParam]

variable {lit : Lit} {frame : Frame}
variable {assignComb : LeafIdx.In aig -> Bool}
variable {assignIn : InputIdx.In aig -> Bool}
variable {assign : InputIdx.In aig -> Frame -> Bool}
variable {valid : lit.validIn aig} {wf : aig.WellFormed}

theorem denoteComb_eq_denoteSeq_of_Comb' {frame : Frame} (comb : aig.Comb) :
    aig.denoteComb lit (assignIn <| ·.val.asInput.castIn aig) valid wf =
    aig.denoteSeq lit frame (fun idx _ => assignIn idx) valid wf := by
  unfold denoteComb denoteSeq
  induction h : lit.var using WellFounded.induction generalizing lit
  exact WellFoundedRelation.wf
  next ih =>
    unfold denoteComb.denoteLit denoteComb.denoteVar denoteSeq.denoteLit denoteSeq.denoteVar
    simp [WellFoundedRelation.rel] at ih
    grind

theorem denoteComb_eq_denoteSeq_of_Comb (comb : aig.Comb) :
    aig.denoteComb lit (assignIn <| ·.val.asInput.castIn aig) valid wf =
    aig.denoteSeq lit 0 (fun idx _ => assignIn idx) valid wf :=
  denoteComb_eq_denoteSeq_of_Comb' comb

/-
We provide a set of theorems for reasoning about `denoteSeq` in terms of `denoteComb`. To prevent
issues proving correctness of mutual recusion, these are broken down with leaf assignment functions
that drop back to `denoteSeq` after one layer of `denoteComb`, but these can be combined to
build the inductive equivalence.
-/

theorem denoteSeq_eq_denoteComb :
    let assignComb (idx : LeafIdx.In aig) : Bool :=
      match h : idx.val, frame with
      | .input idx, _     => assign (idx.castIn aig) frame
      | .latch idx, 0     => aig.denoteSeq (idx.getReset aig) 0 assign
      | .latch idx, n + 1 => aig.denoteSeq (idx.getNext aig)  n assign
    aig.denoteSeq lit frame assign valid wf =
    aig.denoteComb lit assignComb valid wf := by
  simp only
  conv => left; unfold denoteSeq
  conv => right; unfold denoteComb
  induction _ : (frame, lit.var) using WellFounded.induction generalizing frame lit
  exact WellFoundedRelation.wf
  next ih _ =>
    unfold denoteSeq.denoteLit denoteSeq.denoteVar denoteComb.denoteLit denoteComb.denoteVar
    simp_all [WellFoundedRelation.rel, Prod.lex_def, InvImage]
    grind [denoteSeq]

theorem denoteSeq_eq_denoteComb_reset :
    let assignComb (idx : LeafIdx.In aig) : Bool :=
      match h : idx.val with
      | .input idx => assign (idx.castIn aig) 0
      | .latch idx => aig.denoteSeq (idx.getReset aig) 0 assign
    aig.denoteSeq lit 0 assign valid wf =
    aig.denoteComb lit assignComb valid wf := by
  grind only [denoteSeq_eq_denoteComb]

theorem denoteComb_eq_denoteComb_of_eq_le_var (assignComb' : LeafIdx.In aig -> Bool)
    (heq : ∀ {idx} (_ : idx.val.getVar aig ≤ lit.var),
      assignComb idx = assignComb' idx) :
    aig.denoteComb lit assignComb valid wf =
    aig.denoteComb lit assignComb' valid wf := by
  unfold denoteComb
  induction _ : lit.var using WellFounded.induction generalizing lit
  exact WellFoundedRelation.wf
  next ih _ =>
    unfold denoteComb.denoteLit denoteComb.denoteVar
    simp [WellFoundedRelation.rel] at ih
    simp_all
    grind

/--
TODO: This can be derived from a more fine-grained statement about COI.
-/
theorem denoteSeq_eq_denoteSeq_of_eq_le_frame (assign' : InputIdx.In aig -> Frame -> Bool)
    (heq : ∀ {idx frame'} (_ : frame' ≤ frame), assign idx frame' = assign' idx frame') :
    aig.denoteSeq lit frame assign valid wf =
    aig.denoteSeq lit frame assign' valid wf := by
  induction _ : (frame, lit.var) using WellFounded.induction generalizing frame lit
  exact WellFoundedRelation.wf
  next ih _ =>
    simp [WellFoundedRelation.rel, Prod.lex_def, InvImage] at ih
    rw [denoteSeq_eq_denoteComb, denoteSeq_eq_denoteComb]
    apply denoteComb_eq_denoteComb_of_eq_le_var
    simp_all
    grind

local grind_pattern getElem_decls_eq_get => aig.aig.decls[idx]

open Std.Sat AIG in
private theorem denoteComb_eq_std_denote {assign : LeafIdx -> Bool} :
    aig.denoteComb lit (assign ·) valid wf =
    AIG.denote assign (Entrypoint.mk aig.aig <| lit.toRef valid) := by
  unfold denoteComb denote
  induction h : lit.var using WellFounded.induction generalizing lit
  exact WellFoundedRelation.wf
  next ih =>
    unfold denoteComb.denoteLit denoteComb.denoteVar denote.go
    simp [WellFoundedRelation.rel] at ih
    simp_all
    grind [get_eq_getElem_decls, Lit.inverted_mk]

/--
A literal is unsatisfiable in an Aig if for all assignments to inputs and latches its value is
false.
-/
@[expose]
def Unsat (aig : Aig) (lit : Lit) (valid : lit.validIn aig := by grind) (wf : aig.WellFormed := by grind) :=
  ∀ {assign},
    aig.denoteComb lit assign valid wf = false

open Std.Sat AIG in
private theorem Unsat_iff_std_Unsat :
    aig.Unsat lit valid wf ↔
    Entrypoint.Unsat (.mk aig.aig <| lit.toRef valid) := by
  unfold Unsat Entrypoint.Unsat AIG.UnsatAt
  constructor
  · intro h assign
    rw [←denoteComb_eq_std_denote]
    · apply h
    · trivial
  · intro h assign
    let assign' (idx : LeafIdx) :=
      if valid : idx.validIn aig then
        assign ⟨idx, valid⟩
      else
        false
    rw [denoteComb_eq_denoteComb_of_eq_le_var (assign' ·) (by grind only)]
    rw [denoteComb_eq_std_denote]
    apply h
