import Valaig.Aig.Basic
import Valaig.Aig.Lemmas
import Std.Sat.AIG.Basic
import Valaig.Prelude

-- Convert from a Std.Sat.AIG to our sequential Aig

namespace Valaig.Aig

open Std.Sat AIG
variable {α : Type} [DecidableEq α] [Hashable α]

namespace FromStd

inductive RelabelledAtom (aig : AIG α) where
| input
  (symbol : String := "")
| latch
  (next : aig.Ref)
  -- TODO: Support generic reset functions and uninitialised latches not just Bool
  (reset : Bool)
  (symbol : String := "")

@[unbox, grind]
private structure State (stdAig : AIG α) where
  aig : Aig := .empty

  -- A map from variable indices in stdAig (Ref.gate) to Lits in aig
  map : Array Lit := #[]

  -- A map from atoms in the original AIG to their canonical variable in aig
  atomMap : Std.HashMap α Var := .emptyWithCapacity

  -- A map from the variable defined by each latch to its ref in stdAig, to
  -- allow latch finalisation once all nodes have been visited
  latchNexts : Std.HashMap Var stdAig.Ref := .emptyWithCapacity

  hmap : ∀ {x} (_ : x ∈ map), x.validIn aig := by grind
  hlatch : ∀ {l} (_ : l ∈ aig.latches), l.var ∈ latchNexts := by grind
  hatom : ∀ {a} (_ : a ∈ atomMap),
    ∃ (h : atomMap[a].validIn aig), aig[atomMap[a]] matches .atom _ := by grind

namespace State

variable {aig : AIG α}

@[simp, grind]
abbrev size (s : State aig) := s.map.size

@[simp, grind]
def measure (s : State aig) := aig.decls.size - s.size

abbrev Pushed (s : State aig) := { s' : State aig // s'.size = s.size + 1 }

@[always_inline]
def addFalse (s : State aig) : s.Pushed :=
  ⟨{ s with map := s.map.push .false, hmap := by grind}, by grind only [Array.size_push]⟩

@[always_inline]
def addGate (s : State aig) (rhs0 rhs1 : Fanin)
    (h0 : rhs0.gate < s.map.size) (h1 : rhs1.gate < s.map.size) : s.Pushed :=
  let rhs0 := s.map[rhs0.gate]'h0 |>.invert rhs0.invert
  let rhs1 := s.map[rhs1.gate]'h1 |>.invert rhs1.invert
  rlet (aig, lhs) := s.aig.addGate rhs0 rhs1
  let map := s.map.push lhs

  have hmap := by grind only [addGate_validIn, validIn_addGate, Array.mem_push]
  have hlatch := by grind only [addGate_latches_eq]
  have hatom := by grind only [validIn_addGate, addGate_getElem_eq]
  ⟨{ s with aig, map, hmap, hlatch, hatom }, by grind only [Array.size_push]⟩

-- Tries to add an atom that already exists, returns none if it doesn't
@[always_inline]
def tryAddCachedAtom (s : State aig) (atom : α) : Option s.Pushed := do
  rlet h : var ← s.atomMap[atom]?
  let map := s.map.push var.toLit

  have hmap := by
    simp_all
    rintro _ (hold | hnew)
    · exact s.hmap hold
    · have := Std.HashMap.isSome_getElem?_iff_mem.mp (Option.isSome_of_eq_some h)
      simp_all; rw [←h]; cases (s.hatom this); trivial
  return ⟨{ s with map, hmap }, by grind only [Array.size_push]⟩

@[always_inline]
def addInput (s : State aig) (atom : α) (symbol : String) : s.Pushed :=
  let (eq:=_) (aig, input) := s.aig.addInput symbol
  let map := s.map.push input
  let atomMap := s.atomMap.insert atom input

  have hmap := by simp; grind only [addInput_matches_atom, Lit.mk_self_eq_self, validIn_addInput, Lit.mk_ext]
  have hlatch := by grind only [addInput_latches_eq]
  have hatom := by
    intros
    simp only [Std.HashMap.getElem_insert]
    split
    · grind only [addInput_matches_atom]
    · grind only [validIn_addInput, addInput_getElem_eq]
  ⟨{ s with aig, map, atomMap, hmap, hlatch, hatom }, by grind only [Array.size_push]⟩

@[always_inline]
def addLatch (s : State aig) (atom : α) (next : aig.Ref) (reset : Bool) (symbol : String) : s.Pushed :=
  let nextLit := Lit.ofRef next
  let resetLit := Lit.constant reset

  -- We set a fake next state literal at first because we may not have added the logic driving
  -- the next state yet and store it in latchNexts so we can update it subsequently
  let (eq:=_) (aig, latch) := s.aig.addLatch .false resetLit symbol
  let map := s.map.push latch
  let atomMap := s.atomMap.insert atom latch
  let latchNexts := s.latchNexts.insert latch next

  have hmap := by simp; grind only [addLatch_matches_atom, Lit.mk_self_eq_self, validIn_addLatch, Lit.mk_ext]
  have hlatch := by simp; grind only [addLatch_latches_eq_push, Array.mem_push]
  have hatom := by simp; grind only [addLatch_matches_atom, validIn_addLatch, Std.HashMap.getElem_insert, addLatch_getElem_eq]
  ⟨{ aig, map, atomMap, latchNexts, hmap, hlatch, hatom }, by grind only [Array.size_push]⟩

end State

structure Result (stdAig : AIG α) where
  aig : Aig
  refMap : stdAig.Ref -> Lit
  atomMap : α -> Option Var

  hrefvalid : ∀ {ref}, refMap ref |>.validIn aig

end FromStd

open FromStd in
def fromStdAIG (stdAig : AIG α) (relabel : α -> RelabelledAtom stdAig) : Result stdAig :=
  have ⟨state, hstate⟩ := go

  let aig := state.aig.setNexts <| fun latch h =>
    let ref := state.latchNexts[latch.var]'(state.hlatch h)
    have := ref.hgate
    let lit := state.map[ref.gate]'(by omega) |>.invert ref.invert
    ⟨lit, by grind [!Lit.mk_var]⟩

  let refMap (ref : stdAig.Ref) : Lit :=
    have := ref.hgate
    state.map[ref.gate]'(by omega) |>.invert ref.invert

  let atomMap (atom : α) : Option Var := state.atomMap[atom]?

  have hrefvalid : ∀ {ref}, refMap ref |>.validIn aig := by
    simp [refMap]
    grind only [validIn_setNexts, Array.getElem_mem]

  { aig, refMap, atomMap, hrefvalid }

where
  go (s : State stdAig := {}) (h : s.map.size ≤ stdAig.decls.size := by grind) :
      { s : State stdAig // s.map.size = stdAig.decls.size } :=
    let idx := s.map.size
    if hidx : idx ≥ stdAig.decls.size then 
      ⟨s, by omega⟩
    else
      let ⟨s', h⟩ :=
        match heq : stdAig.decls[idx] with
        | .false => s.addFalse
        | .gate rhs0 rhs1 =>
          have hdag := @stdAig.hdag idx rhs0 rhs1 (by omega) heq
          s.addGate rhs0 rhs1 hdag.left hdag.right
        | .atom atom =>
          match h : s.tryAddCachedAtom atom with
          | some s => s
          | none =>
            match relabel atom with
            | .input            symbol => s.addInput atom symbol
            | .latch next reset symbol => s.addLatch atom next reset symbol

      have : s'.measure < s.measure := by grind only [State.measure]
      go s' (by lia)
  termination_by s.measure

/-
@[inline]
def fromStdEntrypoint (entry : Entrypoint α) (relabel : α -> RelabelledAtom entry.aig) :
    (result : FromStdResult entry.aig) × (Lit.In result.aig) :=
  let result := fromStdAIG entry.aig relabel
  let lit := result.refMap entry.ref
  ⟨result, ⟨lit, result.hrefvalid⟩⟩
-/

end Valaig.Aig
