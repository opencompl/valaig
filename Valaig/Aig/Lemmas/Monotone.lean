module

public import Valaig.Aig.Lemmas.Basic
import all Valaig.Aig.Basic

public section
namespace Valaig.Aig

/--
A pair of Aigs are monotone (represented with `old ≤ new`) if all references valid in the old Aig
are also valid in the new Aig and all getters for these references return the same values
-/
structure Monotone (old new : Aig) : Prop where
  nodes : old.nodes ≤ new.nodes
  inputs : old.inputs ≤ new.inputs
  latches : old.latches ≤ new.latches

@[inherit_doc Monotone]
instance : LE Aig where
  le := Monotone

@[simp]
theorem mono_eq {old new : Aig} :
    old.Monotone new ↔ old ≤ new := by
  rfl

instance : Std.IsPreorder Aig := by
  apply Std.IsPreorder.of_le
  <;> constructor
  <;> grind [=_ mono_eq, Monotone]

attribute [grind norm] mono_eq

section Monotone
variable {old new : Aig} (mono : old ≤ new)
include mono

@[simp, grind .]
theorem mono_nodes_mono :
    old.nodes ≤ new.nodes :=
  mono.nodes

@[simp, grind .]
theorem mono_inputs_mono :
    old.inputs ≤ new.inputs :=
  mono.inputs

@[simp, grind .]
theorem mono_latches_mono :
    old.latches ≤ new.latches :=
  mono.latches

@[simp, grind .]
theorem mem_nodes_mono {var : Var} (mem : var ∈ old.nodes) :
    var ∈ new.nodes := by
  grind [mono.nodes]

@[simp, grind .]
theorem mem_inputs_mono {idx : InputIdx} (mem : idx ∈ old.inputs) :
    idx ∈ new.inputs := by
  grind [mono.inputs]

@[simp, grind .]
theorem mem_latches_mono {idx : LatchIdx} (mem : idx ∈ old.latches) :
    idx ∈ new.latches := by
  grind [mono.latches]

@[simp]
theorem getElem_nodes_mono {var : Var} (mem : var ∈ old.nodes) :
    new.nodes[var] = old.nodes[var] := by
  grind [mono.nodes]

grind_pattern getElem_nodes_mono => new.nodes[var], old ≤ new

@[simp]
theorem getElem_inputs_mono {idx : InputIdx} (mem : idx ∈ old.inputs) :
    new.inputs[idx] = old.inputs[idx] := by
  grind [mono.inputs]

grind_pattern getElem_inputs_mono => new.inputs[idx], old ≤ new

@[simp]
theorem getElem_latches_mono {idx : LatchIdx} (mem : idx ∈ old.latches) :
    new.latches[idx] = old.latches[idx] := by
  grind [mono.latches]

grind_pattern getElem_latches_mono => new.latches[idx], old ≤ new

end Monotone
end Valaig.Aig
