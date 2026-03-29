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

variable {var : Var} {lit : Lit} {frame : Frame}
variable {valid : var.validIn aig} {litValid : lit.validIn aig} {wf : aig.WellFormed}

mutual

@[expose]
def denoteCombVar (aig : Aig) (var : Var) (assign : LeafIdx -> Bool)
      (wf : aig.WellFormed := by grind) : Bool :=
    match _ : aig[var]? with
    | none
    | some .false           => false
    | some (.input idx)
    | some (.latch idx)     => assign idx
    | some (.and rhs0 rhs1) => aig.denoteComb rhs0 assign && aig.denoteComb rhs1 assign
  termination_by (var, 0)
  decreasing_by all_goals grind

def denoteComb (aig : Aig) (lit : Lit) (assign : LeafIdx -> Bool)
      (wf : aig.WellFormed := by grind) : Bool :=
    lit.inverted ^^ aig.denoteCombVar lit.var assign wf
  termination_by (lit.var, 1)

end -- mutual

/-
Semantics to elements in the aig for `denoteComb`
-/
section denoteComb
variable {assign : LeafIdx -> Bool}

@[simp, grind =]
theorem denoteComb_eq :
    aig.denoteComb lit assign wf =
    (lit.inverted ^^ aig.denoteCombVar lit.var assign wf) := by
  unfold denoteComb
  grind

@[simp]
theorem denoteCombVar_invalid (invalid : ¬var.validIn aig) :
    aig.denoteCombVar var assign wf = false := by
  unfold denoteCombVar
  grind

grind_pattern denoteCombVar_invalid => aig.denoteCombVar var assign wf, var.validIn aig

@[simp, grind =]
theorem denoteCombVar_constant :
    aig.denoteCombVar .constant assign wf = false := by
  unfold denoteCombVar
  grind

@[simp]
theorem denoteCombVar_get_false (h : aig.get var valid = .false) :
    aig.denoteCombVar var assign wf = false := by
  grind

grind_pattern denoteCombVar_get_false => aig.get var, Node.false, aig.denoteCombVar var assign wf

@[simp]
theorem denoteCombVar_get_input {idx : InputIdx} (h : aig.get var valid = .input idx) :
    aig.denoteCombVar var assign wf = assign idx := by
  unfold denoteCombVar
  grind

grind_pattern denoteCombVar_get_input => aig.get var, Node.input idx, aig.denoteCombVar var assign wf where
  var =/= idx.getVar aig
  idx =/= (_ : Aig).addInput.snd

@[simp, grind =]
theorem denoteCombVar_input_getVar {idx : InputIdx} (valid : idx.validIn aig) :
    aig.denoteCombVar (idx.getVar aig valid) assign wf = assign idx := by
  grind [get_input_getVar, denoteCombVar_get_input]

@[simp]
theorem denoteCombVar_get_latch {idx : LatchIdx} (h : aig.get var valid = .latch idx) :
    aig.denoteCombVar var assign wf = assign idx := by
  unfold denoteCombVar
  grind

grind_pattern denoteCombVar_get_latch => aig.get var, Node.latch idx, aig.denoteCombVar var assign wf where
  var =/= idx.getVar aig
  idx =/= ((_ : Aig).addLatch _ _).snd

@[simp, grind =]
theorem denoteCombVar_latch_getVar {idx : LatchIdx} (valid : idx.validIn aig) :
    aig.denoteCombVar (idx.getVar aig valid) assign wf = assign idx := by
  grind [get_latch_getVar, denoteCombVar_get_latch]

@[simp]
theorem denoteCombVar_get_and {rhs0 rhs1 : Lit} (h : aig.get var valid = .and rhs0 rhs1) :
    aig.denoteCombVar var assign wf =
      (aig.denoteComb rhs0 assign wf && aig.denoteComb rhs1 assign wf) := by
  rw [denoteCombVar]
  grind

grind_pattern denoteCombVar_get_and => aig.get var, Node.and rhs0 rhs1, aig.denoteCombVar var assign wf

theorem denoteCombVar_eq_of_le (assign assign' : LeafIdx -> Bool)
    (h : {idx : LeafIdx} -> (valid : idx.validIn aig) -> idx.getVar aig valid ≤ var -> assign' idx = assign idx) :
    aig.denoteCombVar var assign' wf = aig.denoteCombVar var assign wf := by
  induction var using WellFounded.induction
  exact WellFoundedRelation.wf
  next ih =>
    simp only [WellFoundedRelation.rel] at ih
    unfold denoteCombVar
    split <;> grind (ematch := 10)

@[simp]
theorem denoteCombVar_mono {old new : Aig} {oldWf : old.WellFormed} {newWf : new.WellFormed}
    (mono : old ≤ new) {var : Var} (valid : var.validIn old) :
    new.denoteCombVar var assign newWf = old.denoteCombVar var assign oldWf := by
  induction _ : var using WellFounded.induction generalizing var
  exact WellFoundedRelation.wf
  next ih _ =>
    simp [WellFoundedRelation.rel] at ih
    unfold denoteCombVar
    grind

grind_pattern denoteCombVar_mono => new.denoteCombVar var assign newWf, old ≤ new

open Std.Sat AIG in
private theorem denoteComb_eq_std_denote {assign : LeafIdx -> Bool} :
    aig.denoteComb lit assign wf =
    if valid : lit.validIn aig then
      AIG.denote assign (Entrypoint.mk aig.aig <| lit.toRef valid)
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
      | false => clear ih; grind [get_eq_getElem_decls_false]
      | input idx => clear ih; grind [get_eq_getElem_decls_input]
      | latch idx => clear ih; grind [get_eq_getElem_decls_latch]
      | and rhs0 rhs1 =>
        rw [denoteComb_eq, denoteCombVar_get_and h, ih rhs0.var, ih rhs1.var]
        · unfold AIG.denote
          grind [get_eq_getElem_decls_and valid h]
        all_goals (clear ih; grind)
    case isFalse => grind

@[simp, grind =]
theorem denoteCombVar_addInput'_self {idx : InputIdx} {wf : (aig.addInput' idx).WellFormed} :
    (aig.addInput' idx).denoteCombVar (idx.getVar (aig.addInput' idx)) assign wf =
    assign idx := by
  grind

@[simp, grind =]
theorem denoteCombVar_addLatch'_self {idx : LatchIdx} {next : Lit} {reset : Option Lit}
    (wf : (aig.addLatch' idx next reset).WellFormed) :
    (aig.addLatch' idx next reset).denoteCombVar
      (idx.getVar (aig.addLatch' idx next reset)) assign wf =
    assign idx := by
  grind

@[simp, grind =]
theorem denoteComb_addAnd_self {rhs0 rhs1 : Lit} (h0 : rhs0.validIn aig) (h1 : rhs1.validIn aig)
    (wf' : (aig.addAnd rhs0 rhs1 h0 h1).fst.WellFormed) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.denoteComb (aig.addAnd rhs0 rhs1 h0 h1).snd assign wf' =
    (aig.denoteComb rhs0 assign wf && aig.denoteComb rhs1 assign wf) := by
  have : (aig.addAnd rhs0 rhs1 h0 h1).snd.validIn (aig.addAnd rhs0 rhs1 h0 h1).fst := by grind
  simp only [denoteComb_eq_std_denote, this]
  simp only [addAnd, Lit.toRef_ofRef]
  rw [Std.Sat.AIG.denote_mkAndCached]
  grind [denoteComb_eq_std_denote]

-- TODO: Prove that latch setters don't affect the comb denotation

end denoteComb

mutual

/--
Denotation of the sequential semantics of the Aig in each timeframe, taking a function to assign
values to the inputs in each frame.
-/
def denoteVar (aig : Aig) (var : Var) (frame : Frame) (assign : LeafIdx -> Frame -> Bool)
      (wf : aig.WellFormed := by grind) : Bool :=
    match _ : aig[var]? with
    | none
    | some .false           => false
    | some (.input idx)     => assign idx frame
    | some (.latch idx)     =>
      match frame with
      | 0                   =>
        match _ : idx.getReset aig with
        | none              => assign idx frame
        | some reset        => aig.denote reset 0 assign
      | n + 1               => aig.denote (idx.getNext aig) n assign
    | some (.and rhs0 rhs1) => aig.denote rhs0 frame assign && aig.denote rhs1 frame assign
  termination_by (frame, var, 0)
  decreasing_by all_goals grind

def denote (aig : Aig) (lit : Lit) (frame : Frame) (assign : LeafIdx -> Frame -> Bool)
    (wf : aig.WellFormed := by grind) : Bool :=
  lit.inverted ^^ aig.denoteVar lit.var frame assign
  termination_by (frame, lit.var, 1)

end -- mutual

def denoteResetVar (aig : Aig) (var : Var) (assign : LeafIdx -> Bool) (wf : aig.WellFormed := by grind) : Bool :=
  aig.denoteVar var 0 (fun idx _ => assign idx) wf

@[simp, grind =]
theorem denoteResetVar_eq {var : Var} {assign wf} :
    aig.denoteResetVar var assign wf = aig.denoteVar var 0 (fun idx _ => assign idx) wf := by
  rfl

def denoteReset (aig : Aig) (lit : Lit) (assign : LeafIdx -> Bool) (wf : aig.WellFormed := by grind) : Bool :=
  aig.denote lit 0 (fun idx _ => assign idx) wf

@[simp, grind =]
theorem denoteReset_eq {lit : Lit} {assign wf} :
    aig.denoteReset lit assign wf = aig.denote lit 0 (fun idx _ => assign idx) wf := by
  rfl

theorem denoteReset_eq_denoteResetVar {lit : Lit} {assign wf} :
    aig.denoteReset lit assign wf = (lit.inverted ^^ aig.denoteResetVar lit.var assign wf) := by
  simp [denote]


/--
To allow reasoning about different possible interpretations of the leaves of the Aig (e.g. when
constructing latches where the next state function hasn't been built yet), we design the semantics
around an arbitrary semantics for the leaves.

This function defines the concrete semantics that are used in practice in `denote`/`denoteVar` for
defining sequential computation, allowing an external semantics to be shown equivalent by showing
equivalence to this.
-/
@[expose]
def assignSeq (aig : Aig) (frame : Frame) (assign : LeafIdx -> Frame -> Bool) (wf : aig.WellFormed := by grind) :
    LeafIdx -> Bool :=
  fun idx =>
    match _ : idx with
    | .input idx => assign idx frame
    | .latch idx =>
      if h : idx.validIn aig then
        match frame with
        | 0 =>
          match idx.getReset aig with
          | none       => assign idx 0
          | some reset => aig.denote reset 0 assign
        | n + 1        => aig.denote (idx.getNext aig)  n assign
      else
        false

section denote
variable {assign : LeafIdx -> Frame -> Bool}

@[simp, grind =]
theorem assignSeq_input (idx : InputIdx) :
    (aig.assignSeq frame assign wf) idx = assign idx frame := by
  simp [assignSeq]

@[simp, grind =]
theorem assignSeq_latch {idx : LatchIdx} (valid : idx.validIn aig) :
    (aig.assignSeq frame assign wf) idx =
    match frame with
    | 0 =>
      match idx.getReset aig with
      | none       => assign idx 0
      | some reset => aig.denote reset 0 assign
    | n + 1        => aig.denote (idx.getNext aig) n assign := by
  simp [assignSeq, valid]

@[simp, grind =]
theorem assignSeq_latch_invalid {idx : LatchIdx} (invalid : ¬idx.validIn aig) :
    (aig.assignSeq frame assign wf) idx = false := by
  simp [assignSeq, invalid]

@[simp, grind =]
theorem denote_eq :
    aig.denote lit frame assign wf =
    (lit.inverted ^^ aig.denoteVar lit.var frame assign wf) := by
  rw [denote]

@[local grind =]
theorem denoteVar_eq_denoteCombVar :
    aig.denoteVar var frame assign wf =
    aig.denoteCombVar var (aig.assignSeq frame assign wf) wf := by
  induction h : (frame, var) using WellFounded.induction generalizing var frame
  exact WellFoundedRelation.wf
  next ih =>
    simp [WellFoundedRelation.rel, Prod.lex_def, InvImage] at ih
    rw [denoteVar, denoteCombVar]
    grind

theorem denote_eq_denoteComb :
    aig.denote lit frame assign wf =
    aig.denoteComb lit (aig.assignSeq frame assign wf) wf := by
  simp only [denote_eq, denoteVar_eq_denoteCombVar, denoteComb_eq]

-- TODO: Rebuild all the basic denotations on denoteVar, the same as denoteCombVar

@[simp, grind =]
theorem denoteVar_constant :
    aig.denoteVar .constant frame assign wf = false := by
  grind

@[simp]
theorem denoteVar_invalid (invalid : ¬var.validIn aig) :
    aig.denoteVar var frame assign wf = false := by
  grind

grind_pattern denoteVar_invalid => aig.denoteVar var frame assign wf, var.validIn aig

@[simp]
theorem denoteVar_get_false (h : aig.get var valid = .false) :
    aig.denoteVar var frame assign wf = false := by
  grind

grind_pattern denoteVar_get_false => aig.get var, Node.false, aig.denoteVar var frame assign wf

@[simp]
theorem denoteVar_get_input {idx : InputIdx} (h : aig.get var valid = .input idx) :
    aig.denoteVar var frame assign wf = assign idx frame := by
  grind

grind_pattern denoteVar_get_input => aig.get var, Node.input idx, aig.denoteVar var frame assign wf where
  var =/= idx.getVar aig
  idx =/= (_ : Aig).addInput.snd

@[simp, grind =]
theorem denoteVar_input_getVar {idx : InputIdx} (valid : idx.validIn aig) :
    aig.denoteVar (idx.getVar aig valid) frame assign wf = assign idx frame := by
  grind

@[simp]
theorem denoteVar_get_latch {idx : LatchIdx} (h : aig.get var valid = .latch idx) :
    aig.denoteVar var frame assign wf =
    match frame with
    | 0 =>
      match idx.getReset aig with
      | none       => assign idx 0
      | some reset => aig.denote reset 0 assign wf
    | n + 1 => aig.denote (idx.getNext aig) n assign wf := by
  grind

grind_pattern denoteVar_get_latch => aig.get var, Node.latch idx, aig.denoteVar var frame assign wf where
  var =/= idx.getVar aig
  idx =/= ((_ : Aig).addLatch' _ _ _)

@[simp, grind =]
theorem denoteVar_latch_getVar {idx : LatchIdx} (valid : idx.validIn aig) :
    aig.denoteVar (idx.getVar aig valid) frame assign wf =
    match frame with
    | 0 =>
      match idx.getReset aig with
      | none       => assign idx 0
      | some reset => aig.denote reset 0 assign wf
    | n + 1 => aig.denote (idx.getNext aig) n assign wf := by
  grind

@[simp]
theorem denoteVar_get_and {rhs0 rhs1 : Lit} (h : aig.get var valid = .and rhs0 rhs1) :
    aig.denoteVar var frame assign wf =
      (aig.denote rhs0 frame assign wf && aig.denote rhs1 frame assign wf) := by
  grind

grind_pattern denoteVar_get_and => aig.get var, Node.and rhs0 rhs1, aig.denoteVar var frame assign wf

theorem denoteVar_eq_of_le (assign assign' : LeafIdx -> Frame -> Bool)
    (h : {idx : LeafIdx} -> (valid : idx.validIn aig) -> {frame' : Frame} ->
      frame' < frame ∨ (frame' = frame ∧ idx.getVar aig valid ≤ var) ->
      assign' idx frame' = assign idx frame') :
    aig.denoteVar var frame assign' wf = aig.denoteVar var frame assign wf := by
  induction h : (frame, var) using WellFounded.induction generalizing frame var
  exact WellFoundedRelation.wf
  next ih _ =>
    simp only [WellFoundedRelation.rel, Prod.lex_def, InvImage, sizeOf_nat] at ih
    simp only [denoteVar_eq_denoteCombVar]
    apply denoteCombVar_eq_of_le
    case h =>
      unfold assignSeq
      cases frame
      · grind (splits := 15)
      · grind
    all_goals trivial

section mono
variable {old new : Aig} {oldWf : old.WellFormed} {newWf : new.WellFormed} (mono : old ≤ new)
include mono

@[simp]
theorem assignSeq_mono {idx : LeafIdx} (valid : idx.validIn old) :
    (new.assignSeq frame assign newWf) idx = (old.assignSeq frame assign oldWf) idx := by
  induction h : (frame, idx.getVar old valid) using WellFounded.induction generalizing frame idx
  exact WellFoundedRelation.wf
  next ih =>
    simp only [WellFoundedRelation.rel, Prod.lex_def, InvImage, sizeOf_nat] at ih
    unfold assignSeq
    cases idx with
    | input _ => clear ih; grind only
    | latch idx =>
      cases h : idx.getReset old with
      | none =>
        cases frame <;> grind [denoteCombVar_eq_of_le]
      | some reset =>
        have : reset.var < idx.getVar old := by clear ih; grind
        cases frame <;> grind [denoteCombVar_eq_of_le]

grind_pattern assignSeq_mono => (new.assignSeq frame assign newWf) idx, old ≤ new

@[simp]
theorem denoteVar_mono (var : Var) (valid : var.validIn old) :
    new.denoteVar var frame assign newWf = old.denoteVar var frame assign oldWf := by
  grind [denoteCombVar_mono mono, denoteCombVar_eq_of_le]

grind_pattern denoteVar_mono => new.denoteVar var frame assign newWf, old ≤ new

end mono

@[simp, grind =]
theorem denoteVar_addInput'_self {idx : InputIdx} (wf : (aig.addInput' idx).WellFormed) :
    (aig.addInput' idx).denoteVar (idx.getVar (aig.addInput' idx)) frame assign wf =
    assign idx frame := by
  grind

section addLatch'
variable {idx : LatchIdx} {next : Lit} {reset : Option Lit}

@[simp]
theorem denoteVar_addLatch'_self_none (nextValid : next.validIn aig) (h : ¬idx.validIn aig) :
    let res := aig.addLatch' idx next none
    res.denoteVar (idx.getVar res) frame assign =
    match frame with
    | 0 => assign idx 0
    | n + 1 => aig.denote next n assign wf := by
  grind

@[simp]
theorem denoteVar_addLatch'_self_some {reset : Lit} (nextValid : next.validIn aig)
    (resetValid : reset.validIn aig) (h : ¬idx.validIn aig) :
    let res := aig.addLatch' idx next <| some reset
    res.denoteVar (idx.getVar res) frame assign =
    match frame with
    | 0 => aig.denote reset 0 assign wf
    | n + 1 => aig.denote next n assign wf := by
  grind

theorem denoteVar_addLatch'_self (nextValid : next.validIn aig)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.validIn aig)
    (h : ¬idx.validIn aig) :
    let res := aig.addLatch' idx next reset
    res.denoteVar (idx.getVar res) frame assign =
    match frame with
    | 0 =>
      match reset with
      | none => assign idx 0
      | some lit => aig.denote lit 0 assign wf
    | n + 1 => aig.denote next n assign wf := by
  grind [denoteVar_addLatch'_self_none, denoteVar_addLatch'_self_some]

grind_pattern denoteVar_addLatch'_self =>
  (aig.addLatch' idx next reset).denoteVar (idx.getVar (aig.addLatch' idx next reset)) frame assign

end addLatch'

@[simp, grind =]
theorem denote_addAnd_self {rhs0 rhs1 : Lit} (h0 : rhs0.validIn aig) (h1 : rhs1.validIn aig)
    (wf' : (aig.addAnd rhs0 rhs1 h0 h1).fst.WellFormed) :
    (aig.addAnd rhs0 rhs1 h0 h1).fst.denote (aig.addAnd rhs0 rhs1 h0 h1).snd frame assign wf' =
    (aig.denote rhs0 frame assign wf && aig.denote rhs1 frame assign wf) := by
  grind [denote_eq_denoteComb, denoteCombVar_mono, denoteCombVar_eq_of_le]

end denote

/--
A literal is unsatisfiable in an Aig if for all assignments to inputs and latches its value is
false.
-/
@[expose]
def Unsat (aig : Aig) (lit : Lit) (wf : aig.WellFormed := by grind) :=
  ∀ {assign},
    aig.denoteComb lit assign wf = false

open Std.Sat AIG in
private theorem Unsat_iff_std_Unsat :
    aig.Unsat lit wf ↔
    Entrypoint.Unsat (.mk aig.aig <| lit.toRef litValid) := by
  simp only [Unsat, AIG.Entrypoint.Unsat, AIG.UnsatAt, denoteComb_eq_std_denote, litValid]
  grind only

/--
A literal is unreachable if there is no trace that can reach a state where it is true.
-/
@[expose]
def Unreachable (aig : Aig) (lit : Lit) (wf : aig.WellFormed := by grind) :=
  ∀ {frame assign},
    aig.denote lit frame assign wf = false

theorem Unreachable_of_induction
    (init : ∀ {assign}, aig.denote lit 0 assign wf = false)
    (trans : ∀ {frame assign}, aig.denote lit frame assign wf = false → aig.denote lit (frame + 1) assign wf = false) :
    aig.Unreachable lit wf := by
  intro frame
  induction h : frame generalizing frame <;> grind
