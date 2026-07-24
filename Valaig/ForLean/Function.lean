module

public section

theorem hfunext {α α' : Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : ∀ a, β a} {f' : ∀ a, β' a}
    (hα : α = α') (h : ∀ a a', a ≍ a' → f a ≍ f' a') : f ≍ f' := by
  subst hα
  have : ∀ a, f a ≍ f' a := fun a ↦ h a a (HEq.refl a)
  have : β = β' := by funext a; exact type_eq_of_heq (this a)
  subst this
  grind

end
