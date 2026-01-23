import Valaig.Aig.Basic

namespace Valaig

open Valaig.Aig.Std

attribute [local grind] Aig.Raw.aig
attribute [local grind! .] Std.Sat.AIG.hzero
attribute [local grind! .] Std.Sat.AIG.hconst
attribute [local grind! .] Aig.hfalse
attribute [local grind! .] Aig.hinputs
attribute [local grind! .] Aig.hlatches
attribute [local grind! .] Aig.hnexts

section
variable {aig : Aig.Raw}

@[simp, grind! .]
theorem Var.constant_validIn : Var.constant.validIn aig := by
  simp only [Var.validIn, Var.constant, aig.aig.hzero, Aig.Raw.size]

@[simp, grind! .]
theorem Lit.validIn_mk_validIn {var : Var} (h : var.validIn aig) {invert : Bool} :
    Lit.mk var invert |>.validIn aig := by
  simp_all only [Var.validIn, Aig.Raw.size, Lit.mk_var]

@[simp, grind! .]
theorem Lit.false_validIn : Lit.false.validIn aig := by
  simp

@[simp, grind! .]
theorem Lit.true_validIn : Lit.true.validIn aig := by
  simp

end

namespace Aig

theorem getElem_def {v : Var} (h : v.validIn aig) :
    aig[v] = aig.aig.decls[v.idx] := by
  simp_all only [Raw.instGetElemVar]

attribute [local simp, local grind =] getElem_def
attribute [local simp, local grind] Raw.size
attribute [local simp, local grind .] Array.getElem_of_mem

variable {aig : Aig}

@[simp, grind =]
theorem mem_iff_getElem {a : Std.Sat.AIG.Decl AtomIdx}  :
    a ∈ aig ↔ ∃ (v : Var), ∃ (h : v.validIn aig), aig[v] = a := by
  simp only [instMem, Raw.instMem, Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, h⟩
    exists Var.ofIdx i
  · rintro ⟨v, h⟩
    exists v.idx

theorem nextInputIdx_not_mem_aig :
    .atom (.input aig.nextInputIdx) ∉ aig:= by
  simp
  intro _ h
  have := aig.hinputs.hsurjec h (iarr := aig.nextInputIdx)
  grind only [nextInputIdx]

theorem nextLatchIdx_not_mem_aig :
    .atom (.latch aig.nextLatchIdx) ∉ aig:= by
  simp
  intro _ h
  have := aig.hlatches.hsurjec h (iarr := aig.nextLatchIdx)
  grind only [nextLatchIdx]

theorem decls_unique_inputs {i j : Nat}
    (hi : i < aig.size)
    (hj : j < aig.size)
    (hatom : aig.aig.decls[i] matches .atom (.input _))
    (heq : aig.aig.decls[i] = aig.aig.decls[j]) :
    i = j := by
  have {iarr : Nat} := aig.hinputs.hsurjec hi (iarr := iarr)
  have {iarr : Nat} := aig.hinputs.hsurjec hj (iarr := iarr)
  grind only

theorem decls_unique_latches {i j : Nat}
    (hi : i < aig.size)
    (hj : j < aig.size)
    (hatom : aig.aig.decls[i] matches .atom (.latch _))
    (heq : aig.aig.decls[i] = aig.aig.decls[j]) :
    i = j := by
  have {iarr : Nat} := aig.hlatches.hsurjec hi (iarr := iarr)
  have {iarr : Nat} := aig.hlatches.hsurjec hj (iarr := iarr)
  grind only

theorem decls_unique_atoms {i j : Nat}
    (hi : i < aig.size)
    (hj : j < aig.size)
    (hatom : aig.aig.decls[i] matches .atom _)
    (heq : aig.aig.decls[i] = aig.aig.decls[j]) :
    i = j := by
  match h : aig.aig.decls[i], hatom with
  | .atom (.input _), _ => grind only [decls_unique_inputs]
  | .atom (.latch _), _ => grind only [decls_unique_latches]

theorem inputs_unique {i j : Nat} (hi : i < aig.numInputs) (hj : j < aig.numInputs)
    (heq : aig.inputs[i].var = aig.inputs[j].var) : i = j := by
  grind only [hinputs]

theorem latches_unique {i j : Nat} {hi : i < aig.numLatches} {hj : j < aig.numLatches}
    (heq : aig.latches[i].var = aig.latches[j].var) : i = j := by
  grind only [hlatches]

@[simp, grind! .]
theorem empty_inputs :
    empty.inputs = #[] := by
  simp only [empty]

@[simp, grind! .]
theorem empty_latches :
    empty.latches = #[] := by
  simp only [empty]

@[simp, grind! .]
theorem input_mem_validIn {input : Input} (hmem : input ∈ aig.inputs) :
    input.var.validIn aig := by
  grind only [Array.getElem_of_mem, hinputs, =Var.validIn_def, Raw.size]

@[simp, grind! .]
theorem latch_mem_validIn {latch : Latch} (hmem : latch ∈ aig.latches) :
    latch.var.validIn aig := by
  grind only [Array.getElem_of_mem, hlatches, =Var.validIn_def, Raw.size]

@[simp, grind! .]
theorem input_mem_matches_input {input : Input} (hmem : input ∈ aig.inputs) :
    aig[input.var]'(input_mem_validIn hmem) matches .atom (.input _) := by
  grind only [hinputs, Array.getElem_of_mem, getElem_def]

@[simp, grind! .]
theorem latch_mem_matches_latch {latch : Latch} (hmem : latch ∈ aig.latches) :
    aig[latch.var]'(latch_mem_validIn hmem) matches .atom (.latch _) := by
  grind only [!hlatches, Array.getElem_of_mem, getElem_def]

section
variable {aig : Aig} {var : Var}
variable {symbol : String}

attribute [local simp] mkAtom_eq_decls_push
attribute [local simp] mkAtom_ref_eq_decls_size
attribute [local simp] Std.Sat.AIG.mkAtom_le_size
attribute [local simp] Std.Sat.AIG.mkAndCached_le_size

-- addInput Lemmas

theorem addInput_size_ge :
    (aig.addInput symbol).fst.size ≥ aig.size := by
  simp [addInput]

@[grind! .]
theorem validIn_addInput (h : var.validIn aig) :
    var.validIn (aig.addInput symbol).fst := by
  grind only [addInput_size_ge, Var.validIn_def]

@[grind! .]
theorem addInput_validIn :
    let (aig', input) := aig.addInput symbol
    input.var.validIn aig' := by
  simp [addInput, Var.validIn_def]

@[simp]
theorem addInput_inputs_eq_push :
    let (aig', input) := aig.addInput symbol
    aig'.inputs = aig.inputs.push input := by
  simp [addInput]

@[grind! .]
theorem addInput_mem_inputs :
    let (aig', input) := aig.addInput symbol
    input ∈ aig'.inputs := by
  grind only [addInput_inputs_eq_push, Array.mem_push]

@[grind! .]
theorem addInput_matches_atom_input :
    let (eq:=_) (aig', input) := aig.addInput symbol
    aig'[input.var]'(by grind only [addInput_validIn]) matches .atom (.input _) := by
  apply input_mem_matches_input
  exact addInput_mem_inputs

@[grind! .]
theorem addInput_matches_atom :
    let (eq:=_) (aig', input) := aig.addInput symbol
    aig'[input.var]'(by grind only [addInput_validIn]) matches .atom _ := by
  grind only [addInput_matches_atom_input]

@[simp, grind! .]
theorem addInput_latches_eq :
    (aig.addInput symbol).fst.latches = aig.latches := by
  simp [addInput]

@[simp, grind! .]
theorem addInput_getElem_eq {var : Var} (h : var.validIn aig) :
    (aig.addInput symbol).fst[var]'(validIn_addInput h) = aig[var] := by
  rw [Var.validIn_def] at h
  simp_all [addInput, Array.getElem_push_lt]

@[grind! .]
theorem addInput_mem_eq {decl} (h : decl ∈ aig) :
    decl ∈ (aig.addInput symbol).fst := by
  rw [mem_iff_getElem] at *
  rcases h with ⟨v, ⟨h, heq⟩⟩
  exists v
  exists (validIn_addInput h)
  rw [←heq]
  apply addInput_getElem_eq

-- addLatch Lemmas
section
variable {next : Lit} {reset : Lit} (hnext : next.validIn aig) (hreset : reset.validIn aig)

theorem addLatch_size_ge :
    (aig.addLatch next reset symbol hnext hreset).fst.size ≥ aig.size := by
  simp [addLatch]

@[grind! .]
theorem validIn_addLatch (h : var.validIn aig) :
    var.validIn (aig.addLatch next reset symbol hnext hreset).fst := by
  grind only [addLatch_size_ge, Var.validIn_def]

@[grind! .]
theorem addLatch_validIn:
    let (aig', latch) := aig.addLatch next reset symbol hnext hreset
    latch.var.validIn aig' := by
  simp [addLatch, Var.validIn_def]

@[simp]
theorem addLatch_latches_eq_push :
    let (aig', latch) := aig.addLatch next reset symbol hnext hreset
    aig'.latches = aig.latches.push latch := by
  simp [addLatch]

@[grind! .]
theorem addLatch_mem_latches :
    let (aig', latch) := aig.addLatch next reset symbol hnext hreset
    latch ∈ aig'.latches := by
  grind only [addLatch_latches_eq_push, Array.mem_push]

@[grind! .]
theorem addLatch_matches_atom_latch :
    let (eq:=_) (aig', latch) := aig.addLatch next reset symbol hnext hreset
    aig'[latch.var]'(by grind only [addLatch_validIn]) matches .atom (.latch _) := by
  apply latch_mem_matches_latch
  apply addLatch_mem_latches <;> trivial

@[grind! .]
theorem addLatch_matches_atom :
    let (eq:=_) (aig', latch) := aig.addLatch next reset symbol hnext hreset
    aig'[latch.var]'(by grind only [addLatch_validIn]) matches .atom _ := by
  grind only [addLatch_matches_atom_latch]

@[simp, grind! .]
theorem addLatch_inputs_eq :
    (aig.addLatch next reset symbol hnext hreset).fst.inputs = aig.inputs := by
  simp [addLatch]

@[simp, grind! .]
theorem addLatch_getElem_eq {var : Var} (h : var.validIn aig) :
    have hbound := validIn_addLatch hnext hreset h
    (aig.addLatch next reset symbol hnext hreset).fst[var]'hbound = aig[var] := by
  rw [Var.validIn_def] at h
  simp_all [addLatch, Array.getElem_push_lt]

@[grind! .]
theorem addLatch_mem_eq {decl} (h : decl ∈ aig) :
    decl ∈ (aig.addLatch next reset symbol hnext hreset).fst := by
  rw [mem_iff_getElem] at *
  rcases h with ⟨v, ⟨h, heq⟩⟩
  exists v
  exists validIn_addLatch hnext hreset h
  rw [←heq]
  apply addLatch_getElem_eq

end

-- addGate Lemmas
section
variable {rhs0 rhs1 : Lit} {h0 : rhs0.validIn aig} {h1 : rhs1.validIn aig}

theorem addGate_size_ge :
    (aig.addGate rhs0 rhs1 h0 h1).fst.size ≥ aig.size := by
  simp [addGate]

@[grind! .]
theorem validIn_addGate (h : var.validIn aig) :
    var.validIn (aig.addGate rhs0 rhs1 h0 h1).fst := by
  grind only [addGate_size_ge, Var.validIn_def]

@[grind! .]
theorem addGate_validIn:
    let (aig', gate) := aig.addGate rhs0 rhs1 h0 h1
    gate.validIn aig' := by
  simp [addGate, Var.validIn_def]
  have (r : Std.Sat.AIG.Entrypoint Aig.AtomIdx) := r.ref.hgate
  grind only

@[simp, grind! .]
theorem addGate_inputs_eq :
    (aig.addGate rhs0 rhs1 h0 h1).fst.inputs = aig.inputs := by
  simp [addGate]

@[simp, grind! .]
theorem addGate_latches_eq :
    (aig.addGate rhs0 rhs1 h0 h1).fst.latches = aig.latches := by
  simp [addGate]

@[simp, grind! .]
theorem addGate_getElem_eq {var : Var} (h : var.validIn aig) :
    (aig.addGate rhs0 rhs1 h0 h1).fst[var]'(validIn_addGate h) = aig[var] := by
  apply Std.Sat.AIG.mkGateCached_decl_eq

@[grind! .]
theorem addGate_mem_eq {decl} (h : decl ∈ aig) :
    decl ∈ (aig.addGate rhs0 rhs1 h0 h1).fst := by
  rw [mem_iff_getElem] at *
  rcases h with ⟨v, ⟨h, heq⟩⟩
  exists v
  exists (validIn_addGate h)
  rw [←heq]
  apply addGate_getElem_eq

end

-- setNexts Lemmas
section
variable {f : (latch : Latch) -> latch ∈ aig.latches -> Lit.In aig}

theorem validIn_setNexts (h : var.validIn aig) :
    var.validIn (aig.setNexts f) := by
  simpa only [setNexts, validIn_of_aig_eq aig]

end

end
end Valaig.Aig
