module

@[expose] public section
namespace Valaig
variable {α : Type u}

/--
  Basic set definition as a predicate on a type.
-/
def Set (α : Type u) := α -> Prop

namespace Set

instance : Membership α (Set α) where
  mem s a := s a

theorem mem_iff {s : Set α} {a : α} :
    a ∈ s ↔ s a := by
  rfl

end Valaig.Set
