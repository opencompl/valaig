module

/-
  Basic set definitions adapted from Mathlib.
-/

@[expose] public section
namespace Valaig
variable {α : Type u}

def Set (α : Type u) := α -> Prop

namespace Set

@[implicit_reducible]
def ofPred {α : Type u} (p : α → Prop) : Set α :=
  p

@[implicit_reducible]
protected def Mem (s : Set α) (a : α) : Prop :=
  s a

instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

theorem mem_iff {s : Set α} {a : α} :
    a ∈ s ↔ s a := by
  rfl

@[ext, grind ext]
theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))

instance : EmptyCollection (Set α) :=
  ⟨fun _ => False⟩

instance : Inhabited (Set α) :=
  ⟨fun _ => False⟩

protected def Subset (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

instance : LE (Set α) := ⟨Set.Subset⟩

protected def singleton (a : α) : Set α :=
  fun x => x = a

instance : Singleton α (Set α) := ⟨Set.singleton⟩

protected def union (s1 s2 : Set α) : Set α :=
  fun x => x ∈ s1 ∨ x ∈ s2

instance : Union (Set α) := ⟨Set.union⟩

protected def inter (s1 s2 : Set α) : Set α :=
  fun x => x ∈ s1 ∧ x ∈ s2

instance : Inter (Set α) := ⟨Set.inter⟩

end Valaig.Set
