module

public import Valaig.Aig
public import Valaig.Aig.Lemmas.WellFormed

public section
namespace Valaig

structure WFAig extends raw : Aig where
  wf : raw.WF := by grind

@[expose, simp, grind]
def Aig.toWF (aig : Aig) (wf : aig.WF := by grind) : WFAig :=
  ⟨aig, wf⟩

namespace WFAig
open Aig
variable {aig : WFAig}

@[expose, simp, grind]
def ofAig (aig : Aig) (wf : aig.WF := by grind) : WFAig :=
  ⟨aig, wf⟩

instance : Coe WFAig Aig where
  coe := (·.raw)

@[simp, grind .]
theorem WF :
    aig.raw.WF :=
  aig.wf

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
        | some lit => lit.validIn aig := by grind) :
    WFAig × LatchIdx :=
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

@[always_inline, inherit_doc Aig.addAnd]
def addAnd (aig : WFAig) (lhs rhs : Lit)
    (lvalid : lhs.validIn aig := by grind)
    (rvalid : rhs.validIn aig := by grind) : WFAig × Lit :=
  let (eq:=_) (aig, lit) := aig.raw.addAnd lhs rhs
  (aig.toWF, lit)

@[simp, grind =]
theorem raw_fst_addAnd {lhs rhs : Lit} lvalid rvalid :
    (aig.addAnd lhs rhs lvalid rvalid).fst.raw = (aig.raw.addAnd lhs rhs).fst := by
  rfl

@[simp, grind =]
theorem snd_addAnd {lhs rhs : Lit} lvalid rvalid :
    (aig.addAnd lhs rhs lvalid rvalid).snd = (aig.raw.addAnd lhs rhs).snd := by
  rfl

end Valaig.WFAig
