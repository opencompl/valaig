module

public import Valaig.Aig.Walker
public import Std.Sat.AIG.Basic
import Std.Sat.AIG.CachedLemmas
import Std.Sat.AIG.Cached

public section
namespace Valaig.Sat
open Aig
variable {aig : Aig}

namespace toStd

attribute [local grind! .] Std.Sat.AIG.mkAtomCached_le_size Std.Sat.AIG.mkGateCached_le_size

@[simp, grind! .]
private theorem gate_le_decls_size (entrypoint : Std.Sat.AIG.Entrypoint LeafIdx) :
    entrypoint.ref.gate < entrypoint.aig.decls.size :=
  entrypoint.ref.hgate

@[always_inline]
private def walker (aig : Aig) (reset : Bool) (wf : aig.WF := by grind) : aig.CachingForwardsWalker (Std.Sat.AIG LeafIdx) Lit where
  stateMotive std size le := True
  cacheMotive std size le sm var lt lit :=
    lit.var.idx < std.decls.size

  step var std cache valid size sm cm :=
    let map (lit : Lit) (valid : lit.var < var := by grind) :=
      cache.mapLit lit |>.toRef std

    let res : Std.Sat.AIG.Entrypoint LeafIdx :=
      match _ : aig[var] with
      | .false => .mk std (std.mkConstCached .false)
      | .and rhs0 rhs1 => std.mkGateCached <| .mk (map rhs0) (map rhs1)
      | .input idx => std.mkAtomCached idx
      | .latch idx =>
        if reset then
          match _ : idx.getReset aig with
          | none => std.mkAtomCached idx
          | some lit => .mk std (map lit)
        else
          std.mkAtomCached idx

    (res.aig, .ofRef res.ref)

  stepState := by grind
  stepCache := by intros; (repeat' split) <;> grind
  stepCacheNew := by grind

end toStd

set_option warn.sorry false in
def toStd (aig : Aig) (reset : Bool) (wf : aig.WF := by grind) : (aig' : Std.Sat.AIG LeafIdx) × (Lit.In aig -> aig'.Ref) :=
  let res := (toStd.walker aig reset).walk Std.Sat.AIG.empty (by grind [toStd.walker])
  ⟨res.fst, fun lit => (res.snd.mapLit lit.val).toRef res.fst sorry⟩

end Valaig.Sat
