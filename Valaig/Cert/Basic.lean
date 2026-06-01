module

public import Valaig.Aig
public import Valaig.Aiger
import Valaig.Data.VarCache

public section
namespace Valaig.Cert

private def leafMapping (cert : Aiger) (leaf : Aig.LeafIdx) : Option Lit := do
  let symb ← cert.leafSymbols[leaf]?
  let lit ← symb.skipPrefix? "= "
  let n ← symb.slice lit symb.endPos (by simp) |>.toNat?
  return .ofIdx n

def appendCert (aig : Aiger) (cert : Aiger) : Except String Aiger := do
  -- TODO: Hoist these checks and store them in the types
  if _ : ¬aig.aig.WF then
    throw "Original aig not well formed"
  else if _ : ¬cert.aig.WF then
    throw "Certificate not well formed"

  else if _ : cert.constraints.size > 0 then
    throw "Constraints not supported in certificate"
  else if _ : cert.bads.size ≠ 1 then
    throw "Expected single bad state property"
  else if _ : aig.bads.size ≠ 1 then
    throw "Expected single bad state property"
  else

  let oldBad := aig.bads[0]!.lit

  -- We want to go through every variable, creating a mapping. If the leaf has a definition, we
  -- use that, otherwise we just copy across
  let mut mapping : Data.VarCache Lit := .empty
  let mut prod := aig.aig
  for h : var in cert.aig.iter do
    let map (lit : Lit) :=
      lit.mapTo mapping[lit.var]!

    match cert.aig[var] with
    | .false         =>
      mapping := mapping.push .false
    | .and rhs0 rhs1 =>
      let (aig, var) := prod.addAnd (map rhs0) (map rhs1)
      mapping := mapping.push var
      prod := aig
    | .input idx =>
      match leafMapping cert idx with
      | none =>
        let (aig, idx) := prod.addInput
        mapping := mapping.push (idx.getVar! aig |>.get!)
        prod := aig
      | some lit =>
        mapping := mapping.push lit
    | .latch idx =>
      match leafMapping cert idx with
      | none =>
        throw "latches not supported yet"
      | some lit =>
        mapping := mapping.push lit

  let bad := cert.bads[0]!.lit.mapTo mapping[cert.bads[0]!.lit.var]!
  let (prod', prodBad) := prod.addOr oldBad bad
  let aiger := { Aiger.ofAig prod' with bads := #[.mk prodBad ""] }

  return aiger

end Valaig.Cert

