import Valaig.Aig.Defs
import Valaig.Aig.StdSatLemmas

namespace Valaig.Aig

section
variable {aig aig' : Raw}

theorem hfalse_decls_push {atom}
    (hfalse : aig.SingleFalse)
    (heq : aig'.aig.decls = aig.aig.decls.push atom)
    (hatom : atom ≠ .false) :
    aig'.SingleFalse := by
  grind only [Std.Sat.AIG.hzero, Array.size_push, Array.getElem_push]

theorem hfalse_decls_append
    (hfalse : aig.SingleFalse)
    (hsize : aig'.aig.decls.size ≥ aig.aig.decls.size)
    (hlt :
      ∀ {i} (hi : i < aig.aig.decls.size),
        aig'.aig.decls[i] = aig.aig.decls[i])
    (happend :
      ∀ {i} (_hlow : i ≥ aig.aig.decls.size) (hhigh : i < aig'.aig.decls.size),
        aig'.aig.decls[i] ≠ .false) :
    aig'.SingleFalse := by
  grind only [Std.Sat.AIG.hzero]

end

section

variable {arr arr' : Array α} {idx : α -> Nat}
variable {decls decls': Array (Std.Sat.AIG.Decl AtomIdx)}
variable {mkAtom : Nat -> AtomIdx}

section

variable {atom : Std.Sat.AIG.Decl AtomIdx}
variable (heq : decls' = decls.push atom)
variable (hatom : ∀ {idx}, atom ≠ .atom (mkAtom idx))
include heq hatom

omit hatom in
theorem AtomsInj_unchanged_push (hinjec : AtomsInj arr idx decls mkAtom) :
    AtomsInj arr idx decls' mkAtom := by
  grind only [Array.size_push, Array.getElem_push]

theorem AtomsSur_unchanged_push (hsurjec : AtomsSur arr idx decls mkAtom) :
    AtomsSur arr idx decls' mkAtom := by
  grind only [Array.size_push, Array.getElem_push]

theorem AtomsBij_unchanged_push (hbijec : AtomsBij arr idx decls mkAtom) :
    AtomsBij arr idx decls' mkAtom := by
  constructor
  · exact AtomsInj_unchanged_push heq hbijec.hinjec
  · exact AtomsSur_unchanged_push heq hatom hbijec.hsurjec

end

section

variable {item : α}
variable {atom : Std.Sat.AIG.Decl AtomIdx}
variable (hdecls : decls' = decls.push atom)
variable (harr : arr' = arr.push item)
variable (hidx : idx item = decls.size)
variable (hatom : atom = .atom (mkAtom arr.size))
variable (hMkAtomInj : ∀ {i j}, mkAtom i = mkAtom j ↔ i = j := by simp_all)
include hdecls harr hidx hatom

theorem AtomsInj_push_push (hinjec : AtomsInj arr idx decls mkAtom) :
    AtomsInj arr' idx decls' mkAtom := by
  grind only [Array.size_push, Array.getElem_push]

include hMkAtomInj
theorem AtomsSur_push_push (hsurjec : AtomsSur arr idx decls mkAtom) :
    AtomsSur arr' idx decls' mkAtom := by
  grind only [Array.size_push, Array.getElem_push]

include hMkAtomInj
theorem AtomsBij_push_push (hbijec : AtomsBij arr idx decls mkAtom) :
    AtomsBij arr' idx decls' mkAtom := by
  constructor
  · exact AtomsInj_push_push hdecls harr hidx hatom (hinjec := hbijec.hinjec)
  · exact AtomsSur_push_push hdecls harr hidx hatom (hsurjec := hbijec.hsurjec)

end

section

variable {hsize : decls'.size ≥ decls.size}
variable {hlt : ∀ {i} (hi : i < decls.size), decls'[i] = decls[i]}
variable
  {happend :
    ∀ {i} (_hlow : i ≥ decls.size) (hhigh : i < decls'.size),
    ∀ {idx}, decls'[i] ≠ .atom (mkAtom idx)}
include hsize hlt happend

theorem AtomsInj_unchanged_append (hinjec : AtomsInj arr idx decls mkAtom) :
    AtomsInj arr idx decls' mkAtom := by
  grind only

theorem AtomsSur_unchanged_append (hsurjec : AtomsSur arr idx decls mkAtom) :
    AtomsSur arr idx decls' mkAtom := by
  grind only

theorem AtomsBij_unchanged_append (hbijec : AtomsBij arr idx decls mkAtom) :
    AtomsBij arr idx decls' mkAtom := by
  constructor
  · exact AtomsInj_unchanged_append hbijec.hinjec (hsize := hsize) (hlt := hlt) (happend := happend)
  · exact AtomsSur_unchanged_append hbijec.hsurjec (hsize := hsize) (hlt := hlt) (happend := happend)

end

end

end Valaig.Aig
