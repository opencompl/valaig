module

public import Valaig.Aig
import Valaig.External.Sat.AIG
public import Valaig.Data.Memo

namespace Valaig.Sat
open Aig

namespace toStd

@[simp, grind unfold]
abbrev walker.info (aig : WFAig) (reset : Bool) : Data.Memo.VisitorInfo (Var.In aig) Lit AIG where
  lt := (·.val < ·)
  cacheInv std _ _ lit :=
    std.contains lit.var

open Data.Memo.ActionM in
@[always_inline]
def walker (aig : WFAig) (reset : Bool) : Data.Memo.Visitor (walker.info aig reset) :=
  fun std var => do
    let map (lit : Lit) (valid : lit.var < var := by grind) :
        Data.Memo.ActionM _ _ _ { l : Lit // std.contains l.var } := do
      let new ← get ⟨lit.var, by grind⟩ valid
      return ⟨lit.mapTo new, by grind⟩

    match _ : aig[var.val] with
    | .false => .just .false
    | .and lhs rhs => return std.mkGateCached (←map lhs) (←map rhs)
    | .input idx   => return std.mkAtomCached idx
    | .latch idx   =>
      if _ : reset then
        match _ : idx.getReset aig with
        | none     => return std.mkAtomCached idx
        | some lit => .just (←map lit)
      else
        return std.mkAtomCached idx

variable {reset : Bool}

instance {aig : WFAig} : Data.Memo.WFVisitor (walker aig reset) where
  stateInv := by grind
  cacheInv std var hsi query _ walk hci := by
    apply walker.fun_cases_unfolding
      (motive := fun a => ∀ h, (walker.info aig reset).cacheInv ((a walk hci).value?.get h).fst hsi var ((a walk hci).value?.get h).snd)
    <;> simp [Option.get_unattach]
    <;> grind
  cachePreservation std root var val hsi _ _ _ walk hci := by
    apply walker.fun_cases_unfolding
      (motive := fun a => ∀ h, (walker.info aig reset).cacheInv ((a walk hci).value?.get h).fst hsi var val)
    <;> simp
    <;> grind

end toStd

open Data.Memo in
public def toStd (aig : WFAig) (reset : Bool) (entry : Lit) (valid : entry.validIn aig := by grind) : Std.Sat.AIG.Entrypoint LeafIdx :=
  let w : WFWalker (toStd.walker aig reset) (DFSWalker (toStd.walker aig reset) (Std.HashMap (Var.In aig) _)) :=
    DFSWalker.instWalker
  let s := w.new .empty
  let (eq:=_) (s', lit) := w.visit s ⟨entry.var, valid⟩
  (w.state s').entrypoint (entry.mapTo lit) (by have := w.cacheInv; grind)

end Valaig.Sat
