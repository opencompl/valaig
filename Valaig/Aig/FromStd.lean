module

public import Valaig.Prelude
-- TODO: This shouldn't be necessary but the module system seems broken:
-- https://github.com/leanprover/lean4/issues/12337
import all Valaig.Aig.Basic
public import Valaig.Aig.WellFormed
public import Std.Sat.AIG.Basic

-- Convert from a Std.Sat.AIG to our sequential Aig

public section
namespace Valaig.Aig

open Std.Sat AIG
variable {α : Type} [DecidableEq α] [Hashable α]

namespace FromStd

inductive Leaf (aig : AIG α) where
| input
| latch (next : aig.Ref) (reset : Bool)

@[unbox, grind]
private structure State (stdAig : AIG α) where
  aig : Aig := .empty

  -- A map from variable indices in stdAig (Ref.gate) to Lits in aig
  map : Array Lit := #[]

  -- A map from atoms in the original AIG to their canonical leaf index in aig
  atomMap : Std.HashMap α Aig.LeafIdx := .emptyWithCapacity

  -- A map from the variable defined by each latch to its ref in stdAig, to
  -- allow latch finalisation once all nodes have been visited
  latchNexts : Std.HashMap LatchIdx stdAig.Ref := .emptyWithCapacity

  hwf : aig.WellFormed := by grind

  hmap : ∀ {x} (_ : x ∈ map), x.validIn aig := by grind

  hlatch : ∀ {l : LatchIdx} (_ : l.validIn aig), l ∈ latchNexts := by grind

  hatom : ∀ {a} (_ : a ∈ atomMap), atomMap[a].validIn aig := by grind

namespace State

variable {aig : AIG α}

@[always_inline, simp, grind]
private abbrev size (s : State aig) := s.map.size

@[simp, grind]
private def measure (s : State aig) := aig.decls.size - s.size

private abbrev Pushed (s : State aig) := { s' : State aig // s'.size = s.size + 1 }

@[always_inline]
private def addFalse (s : State aig) : s.Pushed :=
  ⟨{ s with map := s.map.push .false, hmap := by grind}, by grind only [Array.size_push]⟩

@[always_inline]
private def addGate (s : State aig) (rhs0 rhs1 : Fanin)
    (h0 : rhs0.gate < s.map.size) (h1 : rhs1.gate < s.map.size) : s.Pushed :=
  let rhs0 := s.map[rhs0.gate]'h0 |>.invert rhs0.invert
  let rhs1 := s.map[rhs1.gate]'h1 |>.invert rhs1.invert
  rlet (aig, lhs) := s.aig.addAnd rhs0 rhs1
  let map := s.map.push lhs

  have hmap := by
    simp_all only [Array.mem_push, Lit.validIn]
    intro x h
    cases h <;> grind
  have hlatch := by grind
  have hatom := by grind
  have hwf := by grind
  ⟨{ s with aig, map, hmap, hlatch, hatom, hwf }, by grind only [Array.size_push]⟩

-- Tries to add an atom that already exists, returns none if it doesn't
@[always_inline]
private def tryAddCachedAtom (s : State aig) (atom : α) : Option s.Pushed := do
  rlet h : idx ← s.atomMap[atom]?
  let map := s.map.push <| idx.getLit s.aig

  have hmap := by
    simp only [Array.mem_push]
    rintro _ (hold | hnew)
    · exact s.hmap hold
    · grind [@s.hwf.inputsValid, @s.hwf.latchesValid]
  return ⟨{ s with map, hmap }, by grind only [Array.size_push]⟩

@[always_inline]
private def addInput (s : State aig) (atom : α) : s.Pushed :=
  let (eq:=_) (aig, input) := s.aig.addInput
  let map := s.map.push <| input.getLit aig
  let atomMap := s.atomMap.insert atom input

  have hmap := by grind
  have hlatch := by grind
  have hatom := by grind
  have hwf := by grind
  ⟨{ s with aig, map, atomMap, hmap, hlatch, hatom, hwf }, by grind only [Array.size_push]⟩

@[always_inline]
private def addLatch (s : State aig) (atom : α) (next : aig.Ref) (reset : Bool) : s.Pushed :=
  let nextLit := Lit.ofRef next
  let resetLit := Lit.constant reset

  -- We set a fake next state literal at first because we may not have added the logic driving
  -- the next state yet and store it in latchNexts so we can update it subsequently
  let (eq:=_) (aig, latch) := s.aig.addLatch .false resetLit
  let map := s.map.push <| latch.getLit aig
  let atomMap := s.atomMap.insert atom latch
  let latchNexts := s.latchNexts.insert latch next

  have hlatch := by grind
  have hatom := by grind
  have hwf := by grind
  ⟨{ aig, map, atomMap, latchNexts, hmap := by grind, hlatch, hatom, hwf }, by grind⟩

end State

structure Result (stdAig : AIG α) where
  aig : Aig
  refMap : stdAig.Ref -> Lit
  atomMap : α -> Option LeafIdx

  refValid : ∀ {ref}, refMap ref |>.validIn aig
  wellFormed : aig.WellFormed

end FromStd

open FromStd in
def fromStdAIG (stdAig : AIG α) (relabel : α -> Leaf stdAig) : Result stdAig :=
  have ⟨state, hstate⟩ := go

  let refMap (ref : stdAig.Ref) : Lit :=
    have := ref.hgate
    state.map[ref.gate]'(by omega) |>.invert ref.invert

  let atomMap := (state.atomMap[·]?)
  have refValid := by grind
  { aig := state.aig, refMap, atomMap, refValid, wellFormed := state.hwf }

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
            | .input            => s.addInput atom
            | .latch next reset => s.addLatch atom next reset

      have : s'.measure < s.measure := by grind only [State.measure]
      go s' (by lia)
  termination_by s.measure

end Valaig.Aig
