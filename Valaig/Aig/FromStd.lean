import Valaig.Aig.Basic
import Valaig.Aig.Lemmas
import Std.Sat.AIG.Basic

-- Convert from a Std.Sat.AIG to our sequential Aig

namespace Valaig.Aig

variable {α : Type} [DecidableEq α] [Hashable α]

open Std.Sat AIG

inductive RelabelledAtom (aig : AIG α) where
| input
  (symbol : String := "")
  : RelabelledAtom aig
| latch
  (next : aig.Ref)
  (reset : Option aig.Ref := none)
  (symbol : String := "")
  : RelabelledAtom aig

@[unbox, grind]
private structure FromStdState (stdAig : AIG α) where
  aig : Aig := .empty
  -- A map from variable indices in stdAig (Ref.gate) to Vars in aig
  map : Array Var := #[]
  -- A map from the variable defined by each latch to its ref in stdAig, to
  -- allow latch finalisation once all nodes have been visited
  latchNexts : Std.HashMap Var stdAig.Ref := .emptyWithCapacity

  hmap : ∀ {x} (_ : x ∈ map), x.validIn aig := by grind
  hlatch : ∀ {l} (_ : l ∈ aig.latches), l.var ∈ latchNexts := by grind

def fromStdAIG (stdAig : AIG α) (relabel : α -> RelabelledAtom stdAig) : (aig : Aig) × (stdAig.Ref -> Lit.In aig) :=
  have ⟨state, hstate⟩ := go

  let aig := state.aig.finaliseLatches fun latch h =>
    let ref := state.latchNexts[latch.var]'(state.hlatch h)
    have := ref.hgate
    let lit := state.map[ref.gate]'(by omega) |>.toLit ref.invert
    ⟨lit, by grind⟩

  -- TODO: This duplication between this and the above is slightly annoying
  let lookup (ref : stdAig.Ref) : Lit.In aig :=
    have := ref.hgate
    let lit := state.map[ref.gate]'(by omega) |>.toLit ref.invert
    ⟨lit, by grind⟩

  ⟨aig, lookup⟩

where
  go (s : FromStdState stdAig := {}) : { s : FromStdState stdAig // s.map.size ≥ stdAig.decls.size } :=
    let idx := s.map.size
    if hidx : idx ≥ stdAig.decls.size then 
      ⟨s, hidx⟩
    else
      match heq : stdAig.decls[idx] with
      | .false => go { s with map := s.map.push .constant, hmap := by grind }
      | .gate rhs0 rhs1 =>
        have hdag := stdAig.hdag (i := idx) (lhs := rhs0) (rhs := rhs1) (by omega) heq
        let rhs0 := s.map[rhs0.gate]'hdag.left |>.toLit rhs0.invert
        let rhs1 := s.map[rhs1.gate]'hdag.right |>.toLit rhs1.invert
        let (eq:=_) (aig, lhs) := s.aig.addGate rhs0 rhs1
        let map := s.map.push lhs.var
        go { s with aig, map, hmap := by grind, hlatch := by grind }

      | .atom a =>
        match relabel a with
        | .input symbol =>
          let (eq :=_) (aig, lhs) := s.aig.addInput symbol
          let map := s.map.push lhs.var
          go { s with aig, map, hmap := by grind, hlatch := by grind }

        | .latch next reset symbol =>
          let (eq:=_) (aig, lhs) := s.aig.addLatch' (reset.map Lit.ofRef) symbol
          let map := s.map.push lhs.var
          let latchNexts := s.latchNexts.insert lhs next
          let hlatch := by grind [addLatch'_latches_eq_push]
          go { aig, map, latchNexts, hmap := by grind, hlatch }

  termination_by stdAig.decls.size - s.map.size

@[inline]
def fromStdEntrypoint (entry : Entrypoint α) (relabel : α -> RelabelledAtom entry.aig) :
    (aig : Aig) × Lit × (entry.aig.Ref -> Lit.In aig) :=
  let ⟨aig, map⟩ := fromStdAIG entry.aig relabel
  let lit := map entry.ref
  ⟨aig, lit, map⟩

end Valaig.Aig
