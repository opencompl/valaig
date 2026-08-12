module

public import Valaig.Aig
public import Std.Sat.AIG.Basic
import Std.Sat.AIG.CachedLemmas
public import Std.Sat.AIG.Cached
import all Std.Sat.AIG.Cached
public import Valaig.Data.Memo

public section
namespace Valaig.Sat
open Aig

namespace toStd

open Std.Sat AIG

variable {aig : AIG LeafIdx}

private theorem size_empty_le :
    (empty : AIG LeafIdx).decls.size ≤ 1 := by
  unfold AIG.empty
  grind

local grind_pattern size_empty_le => empty.decls.size

private theorem size_mkAtomCached_le {leaf : LeafIdx} :
    (aig.mkAtomCached leaf).aig.decls.size ≤ aig.decls.size + 1 := by
  unfold mkAtomCached
  grind

local grind_pattern size_mkAtomCached_le => (aig.mkAtomCached leaf).aig.decls.size
local grind_pattern mkAtomCached_le_size => (aig.mkAtomCached var).aig.decls.size

private theorem size_mkGateCached_le {input : aig.BinaryInput} :
    (aig.mkGateCached input).aig.decls.size ≤ aig.decls.size + 1 := by
  unfold mkGateCached mkGateCached.go
  grind

local grind_pattern size_mkGateCached_le => (aig.mkGateCached input).aig.decls.size
local grind_pattern mkGateCached_le_size => (aig.mkGateCached input).aig.decls.size

@[simp, grind! .]
private theorem gate_le_decls_size (entrypoint : Entrypoint LeafIdx) :
    entrypoint.ref.gate < entrypoint.aig.decls.size :=
  entrypoint.ref.hgate

@[simp, grind unfold]
abbrev walker.info (aig : WFAig) : Data.Memo.VisitorInfo (Var.In aig) Lit (Std.Sat.AIG LeafIdx) where
  lt := (·.val < ·)
  cacheInv s _ _ lit := lit.var.idx < s.decls.size

open Data.Memo.ActionM in
@[always_inline]
def walker (aig : WFAig) (reset : Bool) : Data.Memo.Visitor (walker.info aig) :=
  fun std var => do
    let map (lit : Lit) (valid : lit.var < var := by grind) := do
      let new ← get ⟨lit.var, by grind⟩ valid
      return lit.mapTo new |>.toRef std

    let just (ref : std.Ref) :=
      .just (.ofRef ref)

    let ret (res : Std.Sat.AIG.Entrypoint LeafIdx) :=
      .pair res.aig (.ofRef res.ref)

    match _ : aig[var.val] with
    | .false       => just <| std.mkConstCached .false
    | .and lhs rhs => ret <| std.mkGateCached <| .mk (←map lhs) (←map rhs)
    | .input idx   => ret <| std.mkAtomCached idx
    | .latch idx   =>
      if _ : reset then
        match _ : idx.getReset aig with
        | none     => ret <| std.mkAtomCached idx
        | some lit => just <| ←map lit
      else
        ret <| std.mkAtomCached idx

variable {reset : Bool}
instance {aig : WFAig} : Data.Memo.WFVisitor (walker aig reset) where
  stateInv := by grind
  cacheInv std var hsi _ _ walk hci := by
    apply walker.fun_cases_unfolding
      (motive := fun a => ∀ h, (walker.info aig).cacheInv ((a walk hci).value?.get h).fst hsi var ((a walk hci).value?.get h).snd)
    <;> simp [Std.Sat.AIG.mkConstCached, std.hzero]
    <;> grind
  cachePreservation std root var val hsi _ _ _ walk hci := by
    intros
    apply walker.fun_cases_unfolding
      (motive := fun a => ∀ h, (walker.info aig).cacheInv ((a walk hci).value?.get h).fst hsi var val)
    <;> simp
    <;> grind

end toStd

open Data.Memo in
def toStd (aig : WFAig) (reset : Bool) (entry : Lit) (valid : entry.validIn aig := by grind) : Std.Sat.AIG.Entrypoint LeafIdx :=
  let w : WFWalker (toStd.walker aig reset) (DFSWalker (toStd.walker aig reset) (Std.HashMap (Var.In aig) _)) :=
    DFSWalker.instWalker
  let s := w.new Std.Sat.AIG.empty
  let (eq:=_) (s', val) := w.visit s ⟨entry.var, valid⟩
  ⟨w.state s', (entry.mapTo val).toRef _ (by have := w.cacheInv; grind)⟩

end Valaig.Sat
