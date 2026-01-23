import Std.Sat.AIG.Basic
import Std.Sat.AIG.CachedGates
import Valaig.Aig.Defs
import Valaig.Aig.DefsLemmas
import Valaig.Aig.RefsLemmas
import Valaig.ForStd

open Valaig.Aig.Std

namespace Valaig.Aig.Raw

attribute [local simp, local grind] Raw.size

@[inline, simp]
abbrev numInputs (aig : Raw) : Nat := aig.inputs.size

@[inline, simp]
abbrev numLatches (aig : Raw) : Nat := aig.latches.size

-- Number of inputs and latches
@[inline, simp, grind]
def numAtoms (aig : Raw) : Nat := aig.numInputs + aig.numLatches

@[inline]
def maxVar (aig : Raw) : Var := .ofIdx (aig.size - 1)

@[inline, simp]
abbrev numConstants (_ : Raw) : Nat := 1

-- Number of inputs, latches and constants
@[inline, simp, grind]
def numLeaves (aig : Raw) : Nat := aig.numAtoms + aig.numConstants

@[inline, simp, grind]
def numGates (aig : Raw) : Nat := aig.size - aig.numLeaves

end Aig.Raw

@[inline, simp]
private abbrev Lit.In.ref {aig : Aig.Raw} (lit : Lit.In aig) : aig.aig.Ref :=
  lit.val.toRef (by grind only [Var.validIn_def'])

namespace Aig

instance Raw.instGetElemVar : GetElem Raw Var (Std.Sat.AIG.Decl AtomIdx) (fun aig var => var.validIn aig) where
  getElem aig var (h := by grind) := aig.aig.decls[var.idx]

@[inline, reducible, simp]
instance instGetElemVar : GetElem Aig Var (Std.Sat.AIG.Decl AtomIdx) (fun aig var => var.validIn aig) where
  getElem aig var (h := by grind) := aig.toRaw[var]'h

instance Raw.instMem : Membership (Std.Sat.AIG.Decl AtomIdx) Raw where
  mem aig decl := decl ∈ aig.aig.decls

@[inline, reducible, simp]
instance instMem : Membership (Std.Sat.AIG.Decl AtomIdx) Aig where
  mem aig decl := decl ∈ aig.toRaw

@[inline]
def VarDef.idx (var : VarDef) (aig : Aig.Raw) (h : var.var.validIn aig := by grind)
    (hatom : aig[var.var] matches .atom _ := by grind) : AtomIdx :=
  match aig[var.var], hatom with
  | .atom idx, _ => idx

@[inline]
def empty : Aig :=
  {
    aig := .empty
    inputs := #[],
    latches := #[],
    hfalse := by simp [Std.Sat.AIG.empty],
    hinputs := by simp [Std.Sat.AIG.empty],
    hlatches := by simp [Std.Sat.AIG.empty],
    hnexts := by simp,
  }

@[inline]
def nextInputIdx (aig : Aig) : Nat :=
  aig.numInputs

@[inline]
def nextLatchIdx (aig : Aig) : Nat :=
  aig.numLatches

@[inline]
def addInput (aig : Aig) (symbol : String := "") : Aig × Input :=
  -- We don't need to use mkAtomCached as nextInputIdx_notIn_decls guarantees
  -- it would be a miss
  let atom := (.input aig.nextInputIdx)
  let res := aig.aig.mkAtom atom
  let input := { var := .ofRef res.ref, symbol }

  let aig := { aig with
    aig := res.aig,
    inputs := aig.inputs.push input,
    hfalse := by apply hfalse_decls_push ?_ (by apply mkAtom_eq_decls_push) <;> grind only [hfalse],
    hinputs := by
      apply AtomsBij_push_push (by apply mkAtom_eq_decls_push) (by trivial) (hbijec := aig.hinputs)
      · grind only [mkAtom_ref_eq_decls_size, Var.ofRef_idx]
      · grind only [nextInputIdx]
    hlatches := by apply AtomsBij_unchanged_push (by apply mkAtom_eq_decls_push) <;> grind only [hlatches],
    hnexts := by grind only [validIn_push aig, mkAtom_eq_decls_push, hnexts]
  }
  (aig, input)

@[inline]
def addLatch (aig : Aig) (next : Lit) (reset : Lit) (symbol : String := "")
    (hnext : next.validIn aig := by grind) (hreset : reset.validIn aig := by grind) : Aig × Latch :=
  -- We don't need to use mkAtomCached as nextLatchIdx_notIn_decls guarantees
  -- it would be a miss
  let res := aig.aig.mkAtom <| .latch aig.nextLatchIdx
  let latch := {
    var := .ofRef res.ref,
    next,
    reset,
    hreset := by simp_all [res, Var.validIn, Var.lt_idx, mkAtom_ref_eq_decls_size, Aig.Raw.size]
    symbol
  }

  let aig := { aig with
    aig := res.aig,
    latches := aig.latches.push latch,
    hfalse := by apply hfalse_decls_push ?_ (by apply mkAtom_eq_decls_push) <;> grind only [hfalse],
    hinputs := by apply AtomsBij_unchanged_push (by apply mkAtom_eq_decls_push) <;> grind only [hinputs],
    hlatches := by
      apply AtomsBij_push_push (by apply mkAtom_eq_decls_push) (by trivial) (hbijec := aig.hlatches)
      · grind only [mkAtom_ref_eq_decls_size, Var.ofRef_idx]
      · grind only [nextLatchIdx]
    hnexts := by grind only [validIn_push aig, mkAtom_eq_decls_push, Array.getElem_push, hnexts]
  }
  (aig, latch)

@[inline]
def addGate (aig : Aig) (rhs0 rhs1 : Lit)
    (h0 : rhs0.validIn aig := by grind) (h1 : rhs1.validIn aig := by grind) :
    Aig × Lit :=
  let res := aig.aig.mkAndCached ⟨rhs0.toRef h0, rhs1.toRef h1⟩

  let aig := { aig with
    aig := res.aig,
    hfalse := by
      apply hfalse_decls_append aig.hfalse
      · grind only [Std.Sat.AIG.mkAndCached_decl_eq]
      · grind only [mkAndCached_matches_gate]
      · apply Std.Sat.AIG.mkAndCached_le_size,
    hinputs := by
      apply AtomsBij_unchanged_append aig.hinputs
      · apply Std.Sat.AIG.mkAndCached_le_size
      · grind only [Std.Sat.AIG.mkAndCached_decl_eq]
      · grind only [mkAndCached_matches_gate],
    hlatches := by
      apply AtomsBij_unchanged_append aig.hlatches
      · apply Std.Sat.AIG.mkAndCached_le_size
      · grind only [Std.Sat.AIG.mkAndCached_decl_eq]
      · grind only [mkAndCached_matches_gate],
    hnexts := by grind only [validIn_of_ge_size aig, Std.Sat.AIG.mkAndCached_le_size, hnexts, Aig.Raw.size]
  }
  (aig, Lit.ofRef res.ref)

@[inline]
def addGateUncached (aig : Aig) (rhs0 rhs1 : Lit)
    (h0 : rhs0.validIn aig := by grind) (h1 : rhs1.validIn aig := by grind) :
    Aig × Lit :=
  let res := aig.aig.mkGate ⟨rhs0.toRef h0, rhs1.toRef h1⟩

  let aig := { aig with
    aig := res.aig,
    hfalse := by
      apply hfalse_decls_append aig.hfalse
      · grind only [Std.Sat.AIG.mkGate_decl_eq]
      · grind only [mkGate_matches_gate]
      · apply Std.Sat.AIG.mkGate_le_size,
    hinputs := by
      apply AtomsBij_unchanged_append aig.hinputs
      · apply Std.Sat.AIG.mkGate_le_size
      · grind only [Std.Sat.AIG.mkGate_decl_eq]
      · grind only [mkGate_matches_gate],
    hlatches := by
      apply AtomsBij_unchanged_append aig.hlatches
      · apply Std.Sat.AIG.mkGate_le_size
      · grind only [Std.Sat.AIG.mkGate_decl_eq]
      · grind only [mkGate_matches_gate]
    hnexts := by grind only [validIn_of_ge_size aig, Std.Sat.AIG.mkGate_le_size, hnexts, Aig.Raw.size]
  }
  (aig, Lit.ofRef res.ref)

@[inline]
def setNext (aig : Aig) (i : LatchIdx) (h : i < aig.numLatches)
    (next : Lit) (hnext : next.validIn aig := by grind) : Aig :=
  let latches := aig.latches.modifyMem i h ({ ·.val with next })
  { aig with
    latches,
    hlatches := by constructor <;> grind [hlatches]
    hnexts := by grind [hnexts, validIn_of_aig_eq aig]
  }

@[inline]
def setNexts (aig : Aig) (f : (latch : Latch) -> latch ∈ aig.latches -> Lit.In aig) : Aig :=
  let modify _ _ latch _ :=
    let next := f latch (by grind only [Array.getElem_mem])
    { latch with next }

  { aig with
    latches := aig.latches.mapMem modify
    hlatches := by constructor <;> grind only [hlatches, Array.size_mapMem, Array.getElem_mapMem]
    hnexts := by grind only [validIn_of_aig_eq aig, Array.getElem_mapMem]
  }

end Aig

end Valaig
