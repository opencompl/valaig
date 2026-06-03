module

public import Valaig.Aig
public import Valaig.Aiger
import Valaig.Data.VarCache

public section
namespace Valaig.Cert

namespace appendCert

@[inline]
private def leafMapping (cert : Aiger) (leaf : Aig.LeafIdx) : Option Lit := do
  let symb ← cert.leafSymbols[leaf]?
  let lit ← symb.skipPrefix? "= "
  let n ← symb.slice lit symb.endPos (by simp) |>.toNat?
  return .ofIdx n

@[always_inline]
private def walker (old : Aig) (cert : Aiger) (certWf : cert.aig.WF := by grind) : cert.aig.CachingForwardsWalker Aig Lit where
  stateMotive aig size le := aig.WF ∧ old ≤ aig
  cacheMotive aig size le sm var lt val := val.validIn aig

  step var aig cache valid size sm cm :=
    match _ : cert.aig[var] with
    | .false => (aig, .false)
    | .and lhs rhs =>
      let (aig, var) := aig.addAndRaw (cache.mapLit lhs) (cache.mapLit rhs)
      (aig, var)

    | .input idx =>
      -- TODO: This should instead be validIn old but naively that breaks linearity
      match _ : leafMapping cert idx |>.filter (·.validIn aig) with
      | none =>
        let (eq:=_) (aig, idx) := aig.addInput
        (aig, idx.getVar aig)
      | some lit => (aig, lit)

    | .latch idx =>
      match _ : leafMapping cert idx |>.filter (·.validIn aig) with
      | none => (aig, panic "latches not supported yet")
      | some lit => (aig, lit)

  stepState := by intros; split <;> grind
  stepCache := by intros; split <;> grind
  stepCacheNew := by simp only [panic_eq]; intros; split <;> grind [Option.filter_eq_some_iff]

private def walk (aig : Aig) (cert : Aiger) (aigWf : aig.WF := by grind) (certWf : cert.aig.WF := by grind) : Aig × Data.VarCache Lit :=
  (walker aig cert).walk aig (by grind [walker])

@[simp, grind =]
private theorem size_walk {aig : Aig} {cert : Aiger} (aigWf : aig.WF) (certWf : cert.aig.WF) :
    (walk aig cert aigWf certWf).snd.size = cert.aig.size := by
  grind [walk]

end appendCert

def appendCert (aig : Aiger) (cert : Aiger) : Except String (Aig × Lit) := do
  -- TODO: Hoist these checks and store them in the types
  if _ : ¬aig.aig.WF then
    throw "Original aig not well formed"
  else if _ : ¬cert.aig.WF then
    throw "Certificate not well formed"

  else if _ : cert.constraints.size > 0 then
    throw "Constraints not supported in certificate"
  else if _ : cert.bads.size ≠ 1 then
    throw "Expected single bad state property"
  else if _ : ¬cert.bads[0].lit.validIn cert.aig then
    throw "Expected cert bad state property to be valid in aig"
  else if _ : aig.bads.size ≠ 1 then
    throw "Expected single bad state property"
  else

  let (eq:=_) (prod, cache) := appendCert.walk aig.aig cert

  let bad := cache.mapLit cert.bads[0].lit
  return (prod, bad)

end Valaig.Cert

