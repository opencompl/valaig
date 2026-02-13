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
@[expose, grind]
def Combinational (aig : Aig) :=
  aig.numLatches = 0

@[grind =]
theorem Combinational_iff_forall_latch_not_valid :
    aig.Combinational ↔ ∀ {latch : LatchIdx}, ¬latch.validIn aig := by
  grind [LatchIdx.numLatches_eq_zero_iff_forall_not_validIn]

mutual

/--
Denotation of the combinational semantics of the Aig, taking a function to assign values to the
input/latches.

The deontation is provided leaves along with a proof that the leaves don't appear after the node
being denoted in the graph to help with termination proofs.
-/
@[expose]
def denoteComb (aig : Aig) (lit : Lit)
    (denoteLeaf : (leaf : LeafIdx.In aig) -> (leaf.val.getVar aig ≤ lit.var) -> Bool)
    (valid : lit.validIn aig := by grind) (wf : aig.WellFormed := by grind) : Bool :=
  denote lit
where
  denote (cur : Lit) (le : cur.var ≤ lit.var := by grind) : Bool :=
    have : cur.validIn aig := by grind [validIn_mono]
    let val :=
      match h : aig[cur.var] with
      | .false => false
      | .input idx => denoteLeaf ⟨.input idx, by grind⟩ (by grind)
      | .latch idx => denoteLeaf ⟨.latch idx, by grind⟩ (by grind)
      | .and rhs0 rhs1 => (denote rhs0) ∧ (denote rhs1)
    val ^^ cur.inverted
  termination_by cur.var
  decreasing_by all_goals grind

/--
Denotation of the sequential semantics of the Aig in each timeframe, taking a function to assign
values to the inputs in each frame.
-/
@[expose]
def denote (aig : Aig) (lit : Lit) (frame : Frame) (denoteInput : InputIdx.In aig -> Frame -> Bool)
    (valid : lit.validIn aig := by grind) (wf : aig.WellFormed := by grind) : Bool :=
  aig.denoteComb lit (denoteLeaf frame)
where
  denoteLeaf {lit : Lit} (frame : Frame) (leaf : LeafIdx.In aig) (leafLt : leaf.val.getVar aig ≤ lit.var) : Bool :=
    match h : leaf.val with
    | .input idx => denoteInput ⟨idx, by grind⟩ frame
    | .latch idx =>
      if h : frame = 0 then
        aig.denoteComb (idx.getReset aig) (denoteLeaf 0)
      else
        aig.denoteComb (idx.getNext aig) (denoteLeaf  (frame - 1))

  termination_by (frame, lit.var)
  decreasing_by all_goals grind

end -- mutual

/--
Denotation of the reset semantics of the Aig, taking a function to assign values to the free
inputs/reset values.
-/
abbrev denoteReset (aig : Aig) (lit : Lit) (denoteInput : InputIdx.In aig -> Bool)
    (valid : lit.validIn aig := by grind) (wf : aig.WellFormed := by grind) : Bool :=
  aig.denote lit 0 (fun idx _ => denoteInput idx) valid wf

variable {lit : Lit} {frame : Frame}
variable {valid : lit.validIn aig} {wf : aig.WellFormed}

theorem denoteComb_eq_denote_of_Combinational {denoteInput : InputIdx.In aig -> Bool}
    (comb : aig.Combinational) :
    aig.denoteComb lit (fun idx _ => denoteInput ⟨idx.val.getInput, by grind⟩) valid wf =
    aig.denote lit 0 (fun idx _ => denoteInput ⟨idx.val, by grind⟩) valid wf := by
  congr
  grind [denote.denoteLeaf]

@[local simp]
private theorem get_decls_def {var : Var} (valid : var.validIn aig) :
    have : var.idx < aig.aig.decls.size := by simp_all [Var.validIn, Aig.size]
    aig.aig.decls[var.idx]'(by simp_all [Var.validIn, Aig.size]) =
    match aig.get var with
    | .false     => .false
    | .input idx => .atom (.input idx)
    | .latch idx => .atom (.latch idx)
    | .and rhs0 rhs1 => .gate rhs0.toFanin rhs1.toFanin := by
  grind [Aig.get]

local grind_pattern get_decls_def => aig.aig.decls[var.idx]

open Std.Sat AIG in
private theorem denoteComb.denote_eq_std_denote {denoteInput : LeafIdx -> Bool}
    {output : Lit} (valid : output.validIn aig) (le : lit.var ≤ output.var) :
    Aig.denoteComb.denote aig output (fun idx _ => denoteInput idx.val) valid wf lit =
    AIG.denote denoteInput (Entrypoint.mk aig.aig <| lit.toRef <| by simp_all [Var.validIn, Aig.size]) := by
  simp [AIG.denote]
  induction h : lit.idx using WellFounded.induction generalizing lit
  · apply WellFoundedRelation.wf
  next ih =>
    rw [denote, denote.go]
    simp_all only [WellFoundedRelation.rel, InvImage]
    split
    · clear ih; grind only [usr get_decls_def]
    · clear ih; grind only [usr get_decls_def]
    · clear ih; grind only [usr get_decls_def]
    · split
      · clear ih; grind only [usr get_decls_def]
      · clear ih; grind only [usr get_decls_def]
      · simp_all
        rename_i litl litr _ _ _ _
        congr
        · have :=
            @ih litl.idx (by grind [Lit.idx_lt_of_var_lt, Lit]) litl
              (by clear ih; grind) (by clear ih; grind) (by rfl)
          grind only [usr get_decls_def, = Lit.toFanin_invert, = Lit.toFanin_gate]
        · have :=
            @ih litr.idx (by grind [Lit.idx_lt_of_var_lt, Lit]) litr
              (by clear ih; grind) (by clear ih; grind) (by rfl)
          grind only [usr get_decls_def, = Lit.toFanin_invert, = Lit.toFanin_gate]

open Std.Sat AIG in
private theorem denoteComb_eq_std_denote {denoteInput : LeafIdx -> Bool} :
    aig.denoteComb lit (fun idx _ => denoteInput idx.val) validIn wf =
    AIG.denote denoteInput (Entrypoint.mk aig.aig (lit.toRef (by simp_all [Var.validIn, Aig.size]))) := by
  rw [denoteComb, denoteComb.denote_eq_std_denote]
  · simp
  · trivial
