module

public import Valaig.Aig
public import Valaig.Aiger
import Valaig.Data.VarCache
import Valaig.Data.DetIter
import Std.Data.HashMap.IteratorLemmas

public section
namespace Valaig.Cert

namespace appendCert

@[inline]
private def leafMapping (cert : Aiger) (leaf : Aig.LeafIdx) : Option Lit := do
  let symb ← cert.leafSymbols[leaf]?
  let lit ← symb.skipPrefix? "= "
  let n ← symb.slice lit symb.endPos (by simp) |>.toNat?
  return .ofIdx n

@[unbox]
structure State (old cert : WFAig) where
  aig : WFAig
  mono : old ≤ aig
  deferredLatches : Std.HashMap Aig.LatchIdx Aig.LatchIdx
  latchKeys : ∀ latch ∈ deferredLatches, latch.validIn cert
  latchVals : ∀ (h : latch ∈ deferredLatches), deferredLatches[latch].validIn aig

attribute [local grind! .] State.mono

@[always_inline, grind, simp]
def State.with {old cert : WFAig} (state : State old cert) (aig : WFAig)
    (mono : state.aig ≤ aig := by grind) : State old cert where
  aig := aig
  mono := by grind
  deferredLatches := state.deferredLatches
  latchKeys := by grind [state.latchKeys]
  latchVals := by grind [state.latchVals]

@[always_inline, grind, simp]
def State.new {cert : WFAig} {aig : WFAig} : State aig cert where
  aig := aig
  mono := by grind
  deferredLatches := .emptyWithCapacity
  latchKeys := by grind
  latchVals := by grind

@[always_inline]
private def walker (old : WFAig) (cert : Aiger) (wf : cert.aig.WF := by grind) :
    cert.aig.CachingForwardsWalker (State old cert.aig.toWF) Lit where
  stateMotive _ _ _ := True
  cacheMotive s size le sm var lt val := val.validIn s.aig

  init := .new
  initState := by grind

  step var s cache valid size sm cm :=
    match _ : cert.aig[var] with
    | .false => (s, .false)
    | .and lhs rhs =>
      let (eq:=_) (aig, var) := s.aig.addAnd (cache.mapLit lhs) (cache.mapLit rhs)
      (s.with aig, var)

    | .input idx =>
      -- TODO: This should instead be validIn old but naively that breaks linearity
      match _ : leafMapping cert idx |>.filter (·.validIn s.aig) with
      | none =>
        let (eq:=_) (aig, idx) := s.aig.addInput
        (s.with aig, idx.getVar aig)
      | some lit => (s, lit)

    | .latch idx =>
      match _ : leafMapping cert idx |>.filter (·.validIn s.aig) with
      | none =>
        let (eq:=_) (aig, idx') := s.aig.addLatch .false none
        ({ s with
           aig,
           deferredLatches := s.deferredLatches.insert idx idx'
           mono := by grind
           latchKeys := by grind [s.latchKeys]
           latchVals := by grind [s.latchVals]
        }, idx'.getVar aig)
      | some lit => (s, lit)

  stepState := by grind
  stepCache := by intros; split <;> grind
  stepCacheNew := by intros; split <;> grind [Option.filter_eq_some_iff]

private def walk (aig : WFAig) (cert : Aiger) (certWf : cert.aig.WF := by grind) :
    State aig cert.aig.toWF × Data.VarCache Lit :=
  (walker aig cert).walk

@[simp, grind =]
private theorem size_walk {aig : WFAig} {cert : Aiger} (certWf : cert.aig.WF) :
    (walk aig cert certWf).snd.size = cert.aig.size := by
  grind [walk]

private def internal (aig : WFAig) (cert : Aiger) (certWf : cert.aig.WF := by grind) : WFAig × Data.VarCache Lit := Id.run do
  let (state, cache) := walk aig cert
  let mut aig : { s : WFAig // ∀ {idx : Aig.LatchIdx}, idx.validIn state.aig → idx.validIn s } := ⟨state.aig, by grind⟩
  for h : e in state.deferredLatches.iter do
    have : e.fst.validIn cert.aig := by grind [Std.HashMap.toList_iter, State]
    have : e.snd.validIn aig := by grind [Std.HashMap.toList_iter, State]
    let aig' := aig.val.setReset e.snd
      ((e.fst.getReset cert.aig).map fun (x : Lit) => if _ : x.var.idx < cache.size then cache.mapLit x else .false)
      sorry sorry
    let next := e.fst.getNext cert.aig
    let next := if _ : next.var.idx < cache.size then cache.mapLit next else .false
    let aig' := aig'.setNext e.snd next sorry sorry
    aig := ⟨aig', by grind⟩
  ⟨aig, cache⟩

end appendCert

set_option warn.sorry false in
def appendCert (aig : Aiger) (cert : Aiger) : Except String (WFAig × Lit) := do
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

  let (eq:=_) (prod, cache) := appendCert.internal aig.aig.toWF cert

  let bad := cache.mapLit cert.bads[0].lit sorry
  return (prod, bad)

end Valaig.Cert

