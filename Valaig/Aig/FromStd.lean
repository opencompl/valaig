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
  (reset : Bool⊕ Option aig.Ref := .inr none)
  (symbol : String := "")
  : RelabelledAtom aig

@[unbox, grind]
private structure FromStdState (stdAig : AIG α) where
  aig : Aig := .empty
  -- A map from variable indices in stdAig (Ref.gate) to Vars in aig
  map : Array Var := #[]
  -- A map from atoms in the original AIG to their canonical variable in aig
  atomMap : Std.HashMap α Var := .emptyWithCapacity
  -- A map from the variable defined by each latch to its ref in stdAig, to
  -- allow latch finalisation once all nodes have been visited
  latchNexts : Std.HashMap Var stdAig.Ref := .emptyWithCapacity

  hmap : ∀ {x} (_ : x ∈ map), x.validIn aig := by grind
  hlatch : ∀ {l} (_ : l ∈ aig.latches), l.var ∈ latchNexts := by grind
  hatom : ∀ {a} (_ : a ∈ atomMap),
    ∃ (h : atomMap[a].validIn aig), aig[atomMap[a]] matches .atom _ := by grind

structure FromStdResult (stdAig : AIG α) where
  aig : Aig
  refMap : stdAig.Ref -> Lit
  atomMap : α -> Option Var

def fromStdAIG (stdAig : AIG α) (relabel : α -> RelabelledAtom stdAig) : FromStdResult stdAig :=
  have ⟨state, hstate⟩ := go

  let aig := state.aig.finaliseLatches fun latch h =>
    let ref := state.latchNexts[latch.var]'(state.hlatch h)
    have := ref.hgate
    let lit := state.map[ref.gate]'(by omega) |>.toLit ref.invert
    ⟨lit, by grind only [Lit.mk_var, Array.getElem_mem]⟩

  let refMap (ref : stdAig.Ref) : Lit :=
    have := ref.hgate
    state.map[ref.gate]'(by omega) |>.toLit ref.invert

  let atomMap (atom : α) : Option Var := state.atomMap[atom]?

  { aig, refMap, atomMap }

where
  go (s : FromStdState stdAig := {}) : { s : FromStdState stdAig // s.map.size ≥ stdAig.decls.size } :=
    let idx := s.map.size
    if hidx : idx ≥ stdAig.decls.size then 
      ⟨s, hidx⟩
    else
      match heq : stdAig.decls[idx] with
      | .false =>
        have hmap := by grind only [Array.mem_push, Var.constant_validIn]
        go { s with map := s.map.push .constant, hmap }
      | .gate rhs0 rhs1 =>
        have hdag := stdAig.hdag (i := idx) (lhs := rhs0) (rhs := rhs1) (by omega) heq
        let rhs0 := s.map[rhs0.gate]'hdag.left |>.toLit rhs0.invert
        let rhs1 := s.map[rhs1.gate]'hdag.right |>.toLit rhs1.invert
        let (eq:=_) (aig, lhs) := s.aig.addGate rhs0 rhs1
        let map := s.map.push lhs.var

        have hmap := by grind only [addGate_validIn, validIn_addGate, Array.mem_push]
        have hlatch := by grind only [addGate_latches_eq]
        have hatom := by grind only [validIn_addGate, addGate_getElem_eq]
        go { s with aig, map, hmap, hlatch, hatom }

      | .atom atom =>
        match h : s.atomMap[atom]? with
        | some var =>
          let map := s.map.push var

          have hmap := by
            simp_all
            rintro _ (hold | hnew)
            · exact s.hmap hold
            · have := Std.HashMap.isSome_getElem?_iff_mem.mp (Option.isSome_of_eq_some h)
              simp_all; rw [←h]; cases (s.hatom this); trivial
          go { s with map, hmap }
        | none =>
          match relabel atom with
          | .input symbol =>
            let (eq:=_) (aig, lhs) := s.aig.addInput symbol
            let map := s.map.push lhs.var
            let atomMap := s.atomMap.insert atom lhs

            have hmap := by grind only [addInput_validIn, validIn_addInput, Array.mem_push]
            have hlatch := by grind only [addInput_latches_eq]
            have hatom := by 
              intros
              simp only [Std.HashMap.getElem_insert]
              split
              · grind only [addInput_matches_atom]
              · grind only [validIn_addInput, addInput_getElem_eq]
            go { s with aig, map, atomMap, hmap, hlatch, hatom }

          | .latch next reset symbol =>
            let reset := match reset with
              | .inl bool => Lit.constant bool
              | .inr var => var.map Lit.ofRef

            let (eq:=_) (aig, lhs) := s.aig.addLatch' reset symbol
            let map := s.map.push lhs.var
            let atomMap := s.atomMap.insert atom lhs
            let latchNexts := s.latchNexts.insert lhs next

            have hmap := by grind only [addLatch'_validIn, validIn_addLatch', Array.mem_push]
            have hlatch := by grind only [addLatch'_latches_eq_push, Std.HashMap.mem_insert, Array.mem_push]
            have hatom := by 
              intros
              simp only [Std.HashMap.getElem_insert]
              split
              · grind only [addLatch'_matches_atom]
              · grind only [validIn_addLatch', addLatch'_getElem_eq]
            go { aig, map, atomMap, latchNexts, hmap, hlatch, hatom }

  termination_by stdAig.decls.size - s.map.size

@[inline]
def fromStdEntrypoint (entry : Entrypoint α) (relabel : α -> RelabelledAtom entry.aig) :
    FromStdResult entry.aig × Lit :=
  let result := fromStdAIG entry.aig relabel
  let lit := result.refMap entry.ref
  (result, lit)

end Valaig.Aig
