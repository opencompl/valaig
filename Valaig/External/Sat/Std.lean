module

public import Valaig.Aig
public import Std.Sat.AIG.Basic
import Std.Sat.AIG.CachedLemmas
import Std.Sat.AIG.Cached
import all Std.Sat.AIG.Cached

public section
namespace Valaig.Sat
open Aig
variable {aig : Aig}

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

@[always_inline]
private def walker (aig : WFAig) (reset : Bool) : TFIWalker aig (Std.Sat.AIG LeafIdx) Lit aig.instNullableLit where
  stateMotive std size le := std.decls.size ≤ max 1 size
  cacheMotive std idx le sm var valid lit :=
    lit.var.idx < std.decls.size

  reset := reset

  init := .empty
  initState := by grind

  step idx var std cache valid lt sm cm :=
    have := aig.instNullableLit

    let map (lit : Lit) (valid : lit.var ∈ aig.TFI var reset := by grind) :=
      cache.mapLit lit |>.toRef std

    let res : Entrypoint LeafIdx :=
      match _ : aig[var] with
      | .false => .mk std (std.mkConstCached .false)
      | .and lhs rhs =>
        std.mkGateCached <| .mk (map lhs) (map rhs)
      | .input idx => std.mkAtomCached idx
      | .latch idx =>
        if _ : reset then
          match _ : idx.getReset aig with
          | none => std.mkAtomCached idx
          | some lit => .mk std (map lit)
        else
          std.mkAtomCached idx

    -- TODO: Fix proofs
    -- have : res.aig.decls.size ≤ std.decls.size + 1 := by sorry

    let lit := .ofRef res.ref
    let property := by sorry
    (res.aig, ⟨lit, property⟩)

  stepState := sorry
  stepCache := sorry
  stepCacheNew := sorry
  -- stepState :=  by intros; (repeat' split) <;> grind [idx_eq_zero_iff_getElem_false]
  -- stepCache := by intros; (repeat' split) <;> grind
  -- stepCacheNew := by grind

end toStd

def toStd (aig : WFAig) (reset : Bool) (entry : Var) (valid : entry.validIn aig := by grind) : (aig' : Std.Sat.AIG LeafIdx) × (Lit.In aig -> aig'.Ref) :=
  let walker := toStd.walker aig reset
  let res := walker.walk entry

  -- have := walker.cacheMotive_walk
  ⟨res.fst, fun lit => (res.snd.mapLit lit.val sorry).toRef res.fst sorry⟩

end Valaig.Sat
