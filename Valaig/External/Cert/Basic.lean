module

public import Valaig.Aig
public import Valaig.External.Aiger
import Valaig.Data.VarCache
import Valaig.Data.DetIter
import Std.Data.HashMap.IteratorLemmas

public section
namespace Valaig.Cert
open Aig

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
  latchVals : ∀ {latch} (h : latch ∈ deferredLatches), deferredLatches[latch].validIn aig ∧ ¬deferredLatches[latch].validIn old

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
        let rst :=
          match _ : idx.getReset cert.aig with
          | none => none
          | some lit => cache.mapLit lit (by grind [show lit.var < var by grind])

        let (eq:=_) (aig, idx') := s.aig.addLatch .false rst (resetValid := by
          subst rst
          split; trivial
          next lit heq => split at heq <;> grind
        )
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

@[simp, grind .]
private theorem validIn_walk {aig : WFAig} {cert : Aiger} {certWf : cert.aig.WF} {var' : Var} h :
    ((walk aig cert certWf).snd[var']'h).var.validIn (walk aig cert certWf).fst.aig  := by
  unfold walk walker
  grind

private def internal (old : WFAig) (cert : Aiger) (certWf : cert.aig.WF := by grind) : WFAig × Data.VarCache Lit :=
  let (eq:=_) (state, cache) := walk old cert

  let aig := state.deferredLatches.iter
    |> Data.DetIter.wrap
    |>.attachWith _ (by simp)
    |>.fold (init := ⟨state.aig, by grind⟩)
    fun (aig : { aig : WFAig // old ≤ aig ∧ aig.nodes = state.aig.nodes ∧ ∀ (idx : LatchIdx), idx.validIn state.aig → idx.validIn aig})
        (elem : { e : (LatchIdx × LatchIdx) // state.deferredLatches[e.fst]? = e.snd }) =>

      let (eq:=_) (key, val) := elem.val
      have : key.validIn cert.aig := by grind [state.latchKeys]
      have : val.validIn aig := by grind [state.latchVals]

      let next := cache.mapLit (key.getNext cert.aig)
      let aig' := aig.val.setNext val next
      ⟨aig', by grind [state.latchVals]⟩

  ⟨aig, cache⟩

@[simp, grind =]
private theorem size_cache_internal {old : WFAig} {cert : Aiger} (certWf : cert.aig.WF) :
    (internal old cert certWf).snd.size = cert.aig.size := by
  simp [internal]

@[simp, grind .]
private theorem validIn_cache_internal {old : WFAig} {cert : Aiger} (certWf : cert.aig.WF) {var : Var} h :
    ((internal old cert certWf).snd[var]'h).validIn (internal old cert certWf).fst := by
  grind [internal]

@[simp, grind .]
private theorem mono_internal {old : WFAig} {cert : Aiger} (certWf : cert.aig.WF) :
    old ≤ (internal old cert certWf).fst := by
  grind [internal, Id.run]

end appendCert

def appendCert (aig cert : Aiger) : Except String (WFAig × Lit) := do
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

  let bad := cache.mapLit cert.bads[0].lit
  return (prod, bad)

@[simp, grind .]
theorem mono_appendCert {aig cert : Aiger} {res} (h : appendCert aig cert = .ok res) :
    aig.aig ≤ res.fst := by
  have := @appendCert.mono_internal (cert := cert)
  revert h
  fun_cases appendCert
  <;> simp [pure, Except.pure]
  <;> grind

@[simp, grind .]
theorem validIn_appendCert_snd {aig cert : Aiger} {res} (h : appendCert aig cert = .ok res) :
    res.snd.validIn res.fst := by
  revert h
  fun_cases appendCert
  <;> simp [pure, Except.pure]
  <;> grind

end Valaig.Cert

