module

public import Valaig.Aig.Core.Basic
import Valaig.Aig.Core.Lemmas.Basic

public section
namespace Valaig.Aig

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

@[grind .]
theorem mono_nodes_mono :
    old.nodes ≤ new.nodes :=
  mono.nodes

@[grind .]
theorem mono_inputs_mono :
    old.inputs ≤ new.inputs :=
  mono.inputs

@[grind .]
theorem mono_latches_mono :
    old.latches ≤ new.latches :=
  mono.latches

@[grind .]
theorem size_nodes_mono :
    old.nodes.size ≤ new.nodes.size :=
  mono.nodes.sized

grind_pattern size_nodes_mono => new.size, old ≤ new

@[grind .]
theorem size_inputs_mono :
    old.inputs.size ≤ new.inputs.size :=
  mono.inputs.sized

grind_pattern size_inputs_mono => new.size, old ≤ new

@[grind .]
theorem size_latches_mono :
    old.latches.size ≤ new.latches.size :=
  mono.latches.sized

grind_pattern size_latches_mono => new.size, old ≤ new

@[grind .]
theorem mem_nodes_mono {var : Var} (mem : var ∈ old.nodes) :
    var ∈ new.nodes := by
  grind [mono.nodes]

@[grind .]
theorem mem_inputs_mono {idx : InputIdx} (mem : idx ∈ old.inputs) :
    idx ∈ new.inputs := by
  grind [mono.inputs]

@[grind .]
theorem mem_latches_mono {idx : LatchIdx} (mem : idx ∈ old.latches) :
    idx ∈ new.latches := by
  grind [mono.latches]

theorem getElem_nodes_mono {var : Var} (mem : var ∈ old.nodes) :
    new.nodes[var] = old.nodes[var] := by
  grind [mono.nodes]

grind_pattern getElem_nodes_mono => new.nodes[var], old ≤ new

theorem getElem_inputs_mono {idx : InputIdx} (mem : idx ∈ old.inputs) :
    new.inputs[idx] = old.inputs[idx] := by
  grind [mono.inputs]

grind_pattern getElem_inputs_mono => new.inputs[idx], old ≤ new

theorem getElem_latches_mono {idx : LatchIdx} (mem : idx ∈ old.latches) :
    new.latches[idx] = old.latches[idx] := by
  grind [mono.latches]

grind_pattern getElem_latches_mono => new.latches[idx], old ≤ new

end Monotone
end Valaig.Aig
