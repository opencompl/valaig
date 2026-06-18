module

public import Valaig.Aig.Core.Basic
public import Valaig.Aig.Core.Lemmas
import Valaig.Aig.Core.TwoLevelSimp
import all Valaig.Aig.Core.Basic

public section
namespace Valaig

structure WFAig extends raw : Aig where
  wf : raw.WF := by grind

@[always_inline]
def Aig.toWF (aig : Aig) (wf : aig.WF := by grind) : WFAig :=
  ⟨aig, wf⟩

@[simp, grind =]
theorem Aig.raw_toWF {aig : Aig} wf :
    (toWF aig wf).raw = aig := by
  rfl

namespace WFAig
open Aig
variable {aig : WFAig}

@[always_inline]
def ofAig (aig : Aig) (wf : aig.WF := by grind) : WFAig :=
  ⟨aig, wf⟩

@[simp, grind =]
theorem raw_ofAig {aig : Aig} wf :
    (ofAig aig wf).raw = aig := by
  rfl

instance : Coe WFAig Aig where
  coe := (·.raw)

@[simp, grind! .]
theorem is_WF :
    aig.raw.WF :=
  aig.wf

@[always_inline]
instance : Decidable aig.WF :=
  isTrue aig.wf

@[inherit_doc Aig.instLE]
instance : LE WFAig where
  le a b := a.raw ≤ b.raw

@[simp, grind =]
theorem le_iff {a b : WFAig} :
    a ≤ b ↔ a.raw ≤ b.raw := by
  rfl

@[always_inline, inherit_doc Aig.instGetElemVar]
instance instGetElemVar : GetElem WFAig Var Node (fun aig var => var.validIn aig) where
  getElem aig var h := aig.raw[var]'h

@[simp, grind =]
theorem getElem_eq {var : Var} h :
    aig[var]'h = aig.raw[var]'h := by
  rfl

@[always_inline, inherit_doc Aig.empty]
def empty : WFAig :=
  Aig.empty.toWF

@[simp, grind =]
theorem raw_empty :
    empty.raw = .empty := by
  rfl

@[always_inline]
instance : Inhabited WFAig where
  default := empty

@[always_inline, inherit_doc Aig.setNext]
def setNext (aig : WFAig) (idx : LatchIdx) (next : Lit) (valid : idx.validIn aig := by grind)
    (nextValid : next.validIn aig := by grind) : WFAig :=
  aig.raw.setNext idx next |>.toWF

@[simp, grind =]
theorem raw_setNext {idx : LatchIdx} {next : Lit} valid nextValid :
    (aig.setNext idx next valid nextValid).raw = aig.raw.setNext idx next := by
  rfl

@[always_inline, inherit_doc Aig.setReset]
def setReset (aig : WFAig) (idx : LatchIdx) (reset : Option Lit) (valid : idx.validIn aig := by grind)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.var < idx.getVar aig := by grind) : WFAig :=
  aig.raw.setReset idx reset |>.toWF

@[simp, grind =]
theorem raw_setReset {idx : LatchIdx} {reset : Option Lit} valid resetValid :
    (aig.setReset idx reset valid resetValid).raw = aig.raw.setReset idx reset := by
  rfl

@[always_inline, inherit_doc Aig.addInput]
def addInput (aig : WFAig) : WFAig × InputIdx :=
  let (eq:=_) (aig, idx) := aig.raw.addInput
  (aig.toWF, idx)

@[simp, grind =]
theorem raw_fst_addInput :
    aig.addInput.fst.raw = aig.raw.addInput.fst := by
  rfl

@[simp, grind =]
theorem snd_addInput :
    aig.addInput.snd = aig.raw.addInput.snd := by
  rfl

@[always_inline, inherit_doc Aig.addLatch]
def addLatch (aig : WFAig) (next : Lit) (reset : Option Lit := none)
    (nextValid : next.validIn aig := by grind)
    (resetValid :
        match reset with
        | none => True
        | some lit => lit.validIn aig := by grind) : WFAig × LatchIdx :=
  let (eq:=_) (aig, idx) := aig.raw.addLatch next reset
  (aig.toWF, idx)

@[simp, grind =]
theorem raw_fst_addLatch {next : Lit} {reset : Option Lit} nextValid resetValid :
    (aig.addLatch next reset nextValid resetValid).fst.raw = (aig.raw.addLatch next reset).fst := by
  rfl

@[simp, grind =]
theorem snd_addLatch {next : Lit} {reset : Option Lit} nextValid resetValid :
    (aig.addLatch next reset nextValid resetValid).snd = (aig.raw.addLatch next reset).snd := by
  rfl

@[always_inline, inherit_doc Aig.addAndRaw]
def addAndRaw (aig : WFAig) (lhs rhs : Lit)
    (lvalid : lhs.validIn aig := by grind)
    (rvalid : rhs.validIn aig := by grind) : WFAig × Var :=
  let (eq:=_) (aig, var) := aig.raw.addAndRaw lhs rhs
  (aig.toWF, var)

@[simp, grind =]
theorem raw_fst_addAndRaw {lhs rhs : Lit} lvalid rvalid :
    (aig.addAndRaw lhs rhs lvalid rvalid).fst.raw = (aig.raw.addAndRaw lhs rhs).fst := by
  rfl

@[simp, grind =]
theorem snd_addAndRaw {lhs rhs : Lit} lvalid rvalid :
    (aig.addAndRaw lhs rhs lvalid rvalid).snd = (aig.raw.addAndRaw lhs rhs).snd := by
  rfl

-- We reimplement addAnd for WFAig to remove the runtime bounds checks
@[inherit_doc Aig.addAnd]
def addAnd (aig : WFAig) (lhs rhs : @&Lit)
    (lvalid : lhs.validIn aig := by grind)
    (rvalid : rhs.validIn aig := by grind) : WFAig × Lit :=
  match TwoLevelSimp.simplifyAnd lhs rhs (aig.asAnd lhs.var) (aig.asAnd rhs.var) with
  | .lit lit => (aig, lit)
  | .and l r => let (aig, var) := aig.addAndRaw l r sorry sorry; (aig, var)

@[simp, grind =]
theorem raw_fst_addAnd {lhs rhs : Lit} lvalid rvalid :
    (aig.addAnd lhs rhs lvalid rvalid).fst.raw = (aig.raw.addAnd lhs rhs).fst := by
  simp only [addAnd, Aig.addAnd]
  grind

@[simp, grind =]
theorem snd_addAnd {lhs rhs : Lit} lvalid rvalid :
    (aig.addAnd lhs rhs lvalid rvalid).snd = (aig.raw.addAnd lhs rhs).snd := by
  simp only [addAnd, Aig.addAnd]
  grind

@[always_inline, inherit_doc Aig.inputToLatch]
def inputToLatch (aig : WFAig) (idx : InputIdx) (next : Lit) (reset : Option Lit := none)
    (valid : idx.validIn aig := by grind)
    (varValid : (idx.getVar aig).validIn aig := by grind)
    (nextValid : next.validIn aig := by grind)
    (resetValid :
      match reset with
      | none => True
      | some lit => lit.var < idx.getVar aig := by grind) : WFAig × LatchIdx :=
  let (eq:=_) (aig, latch) := aig.raw.inputToLatch idx next reset
  (aig.toWF, latch)

@[simp, grind =]
theorem raw_fst_inputToLatch {idx : InputIdx} {next : Lit} {reset : Option Lit} valid varValid nextValid resetValid :
    (aig.inputToLatch idx next reset valid varValid nextValid resetValid).fst.raw =
    (aig.raw.inputToLatch idx next reset).fst := by
  rfl

@[simp, grind =]
theorem snd_inputToLatch {idx : InputIdx} {next : Lit} {reset : Option Lit} valid varValid nextValid resetValid :
    (aig.inputToLatch idx next reset valid varValid nextValid resetValid).snd = (aig.raw.inputToLatch idx next reset).snd := by
  rfl

@[always_inline, inherit_doc Aig.inputToAnd]
def inputToAnd (aig : WFAig) (idx : InputIdx) (lhs rhs : Lit)
    (valid : idx.validIn aig := by grind)
    (varValid : (idx.getVar aig).validIn aig := by grind)
    (lvalid : lhs.var < idx.getVar aig := by grind)
    (rvalid : rhs.var < idx.getVar aig := by grind) : WFAig :=
  aig.raw.inputToAnd idx lhs rhs |>.toWF

@[simp, grind =]
theorem raw_inputToAnd {idx : InputIdx} {lhs rhs : Lit} valid varValid lvalid rvalid :
    (aig.inputToAnd idx lhs rhs valid varValid lvalid rvalid).raw = aig.raw.inputToAnd idx lhs rhs:= by
  rfl

@[always_inline, inherit_doc Aig.changeInputIdx]
def changeInputIdx (aig : WFAig) (old new : InputIdx)
    (valid : old.validIn aig := by grind)
    (varValid : (old.getVar aig).validIn aig := by grind)
    (unused : ¬new.validIn aig ∨ old = new := by grind) : WFAig :=
  aig.raw.changeInputIdx old new |>.toWF

@[simp, grind =]
theorem raw_changeInputIdx {old new : InputIdx} valid varValid unused :
    (aig.changeInputIdx old new valid varValid unused).raw = aig.raw.changeInputIdx old new := by
  rfl

@[always_inline, inherit_doc Aig.latchToInput]
def latchToInput (aig : WFAig) (idx : LatchIdx)
    (valid : idx.validIn aig := by grind)
    (varValid : (idx.getVar aig).validIn aig := by grind) : WFAig × InputIdx :=
  let (eq:=_) (aig, idx) := aig.raw.latchToInput idx
  (aig.toWF, idx)

@[simp, grind =]
theorem raw_fst_latchToInput {idx : LatchIdx} valid varValid :
    (aig.latchToInput idx valid varValid).fst.raw = (aig.raw.latchToInput idx).fst := by
  rfl

@[simp, grind =]
theorem snd_latchToInput {idx : LatchIdx} valid varValid :
    (aig.latchToInput idx valid varValid).snd = (aig.raw.latchToInput idx).snd := by
  rfl

@[always_inline, inherit_doc Aig.latchToAnd]
def latchToAnd (aig : WFAig) (idx : LatchIdx) (lhs rhs : Lit)
    (valid : idx.validIn aig := by grind)
    (varValid : (idx.getVar aig).validIn aig := by grind)
    (lvalid : lhs.var < idx.getVar aig := by grind)
    (rvalid : rhs.var < idx.getVar aig := by grind) : WFAig :=
  aig.raw.latchToAnd idx lhs rhs |>.toWF

@[simp, grind =]
theorem raw_latchToAnd {idx : LatchIdx} {lhs rhs : Lit} valid varValid lvalid rvalid :
    (aig.latchToAnd idx lhs rhs valid varValid lvalid rvalid).raw = aig.raw.latchToAnd idx lhs rhs:= by
  rfl

@[always_inline, inherit_doc Aig.changeLatchIdx]
def changeLatchIdx (aig : WFAig) (old new : LatchIdx)
    (valid : old.validIn aig := by grind)
    (varValid : (old.getVar aig).validIn aig := by grind)
    (unused : ¬new.validIn aig ∨ old = new := by grind) : WFAig :=
  aig.raw.changeLatchIdx old new |>.toWF

@[simp, grind =]
theorem raw_changeLatchIdx {old new : LatchIdx} valid varValid unused :
    (aig.changeLatchIdx old new valid varValid unused).raw = aig.raw.changeLatchIdx old new := by
  rfl

@[always_inline, inherit_doc Aig.andToInput]
def andToInput (aig : WFAig) (var : Var)
    (valid : var.validIn aig := by grind)
    (isAnd : aig[var] matches .and _ _ := by grind) : WFAig × InputIdx :=
  let (eq:=_) (aig, idx) := aig.raw.andToInput var
  (aig.toWF, idx)

@[simp, grind =]
theorem raw_fst_andToInput {var : Var} valid isAnd :
    (aig.andToInput var valid isAnd).fst.raw = (aig.raw.andToInput var).fst := by
  rfl

@[simp, grind =]
theorem snd_andToInput {var : Var} valid isAnd :
    (aig.andToInput var valid isAnd).snd = (aig.raw.andToInput var).snd := by
  rfl

@[always_inline, inherit_doc Aig.andToLatch]
def andToLatch (aig : WFAig) (var : Var) (next : Lit) (reset : Option Lit)
    (valid : var.validIn aig := by grind)
    (nextValid : next.validIn aig := by grind)
    (resetValid :
        match reset with
        | none => True
        | some lit => lit.var < var := by grind)
    (isAnd : aig[var] matches .and _ _ := by grind) : WFAig × LatchIdx :=
  let (eq:=_) (aig, idx) := aig.raw.andToLatch var next reset
  (aig.toWF, idx)

@[simp, grind =]
theorem raw_fst_andToLatch {var : Var} {next : Lit} {reset : Option Lit} valid nextValid resetValid isAnd :
    (aig.andToLatch var next reset valid nextValid resetValid isAnd).fst.raw =
    (aig.raw.andToLatch var next reset).fst := by
  rfl

@[simp, grind =]
theorem snd_andToLatch {var : Var} {next : Lit} {reset : Option Lit} valid nextValid resetValid isAnd :
    (aig.andToLatch var next reset valid nextValid resetValid isAnd).snd =
    (aig.raw.andToLatch var next reset).snd := by
  rfl

@[always_inline, inherit_doc Aig.rewriteAnd]
def rewriteAnd (aig : WFAig) (var : Var) (lhs rhs : Lit)
    (valid : var.validIn aig := by grind)
    (isAnd : aig[var] matches .and _ _ := by grind)
    (lvalid : lhs.var < var := by grind)
    (rvalid : rhs.var < var := by grind) : WFAig :=
  aig.raw.rewriteAnd var lhs rhs |>.toWF

@[simp, grind =]
theorem raw_rewriteAnd {var : Var} {lhs rhs : Lit} valid isAnd lvalid rvalid :
    (aig.rewriteAnd var lhs rhs valid isAnd lvalid rvalid).raw = aig.raw.rewriteAnd var lhs rhs := by
  rfl

end Valaig.WFAig
