module

public import Valaig.Aig
public import Std.Sat.AIG.Basic
import Std.Sat.AIG.CachedLemmas
import Std.Sat.AIG.Cached

public section
namespace Valaig.Sat
open Aig
variable {aig : Aig}

namespace toStd

attribute [local grind! .] Std.Sat.AIG.mkAtom_le_size Std.Sat.AIG.mkGateCached_le_size

@[simp, grind! .]
private theorem gate_le_decls_size (entrypoint : Std.Sat.AIG.Entrypoint LeafIdx) :
    entrypoint.ref.gate < entrypoint.aig.decls.size :=
  entrypoint.ref.hgate

@[always_inline]
private def walker (aig : WFAig) (reset : Bool) : aig.CachingForwardsWalker (Std.Sat.AIG LeafIdx) Lit where
  stateMotive std size le := True
  cacheMotive std size le sm var lt lit :=
    lit.var.idx < std.decls.size

  init := .empty
  initState := by grind

  step var std cache valid size sm cm :=
    let map (lit : Lit) (valid : lit.var < var := by grind) :=
      cache.mapLit lit |>.toRef std

    let res : Std.Sat.AIG.Entrypoint LeafIdx :=
      match _ : aig[var] with
      | .false => .mk std (std.mkConstCached .false)
      | .and lhs rhs => std.mkGateCached <| .mk (map lhs) (map rhs)
      | .input idx => std.mkAtom idx
      | .latch idx =>
        if reset then
          match _ : idx.getReset aig with
          | none => std.mkAtom idx
          | some lit => .mk std (map lit)
        else
          std.mkAtom idx

    (res.aig, .ofRef res.ref)

  stepState := by grind
  stepCache := by intros; (repeat' split) <;> grind
  stepCacheNew := by grind

end toStd

def toStd (aig : WFAig) (reset : Bool) : (aig' : Std.Sat.AIG LeafIdx) × (Lit.In aig -> aig'.Ref) :=
  let walker := toStd.walker aig reset
  let res := walker.walk

  have := walker.cacheMotive_walk
  ⟨res.fst, fun lit => (res.snd.mapLit lit.val).toRef res.fst (by grind [toStd.walker])⟩

end Valaig.Sat
