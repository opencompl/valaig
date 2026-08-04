module

public section

@[simp]
theorem Prod.fst_dite {α β : Type _} {c : Prop} [Decidable c] {a : c -> (α × β)} {b : ¬c -> (α × β)} :
    (dite c a b).fst = dite c (fun h => (a h).fst) (fun h => (b h).fst) := by
  grind

@[simp]
theorem Prod.snd_dite {α β : Type _} {c : Prop} [Decidable c] {a : c -> (α × β)} {b : ¬c -> (α × β)} :
    (dite c a b).snd = dite c (fun h => (a h).snd) (fun h => (b h).snd) := by
  grind
