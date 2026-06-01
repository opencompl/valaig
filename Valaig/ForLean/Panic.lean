module

public section

@[simp, grind =]
theorem panic_eq {α : Type} [Inhabited α] {msg : String} :
    panic (α := α) msg = Inhabited.default := by
  grind [panic, panicCore]

namespace Valaig

def panicAt {α : Type} [Inhabited α] (loc msg : String) : α :=
    panic s!"paniced at {loc}: {msg}"

@[simp, grind =]
theorem panicAt_eq {α : Type} [Inhabited α] {loc msg : String} :
    panicAt (α := α) loc msg = Inhabited.default := by
  grind [panicAt]

set_option linter.unusedVariables false in
@[always_inline]
def checkOrPanic (p : Prop) [Decidable p] (loc msg : String) : Option { u : Unit // p } :=
  if h : p then
    some ⟨(), h⟩
  else
    panicAt loc msg

@[simp, grind =]
theorem checkOrPanic_eq {p : Prop} [Decidable p] {loc msg : String} :
    checkOrPanic p loc msg = if h : p then some ⟨(), h⟩ else none := by
  grind [checkOrPanic]

set_option linter.unusedVariables false in
@[grind .]
theorem checkOrPanic_some {p : Prop} [Decidable p] {loc msg : String} u
    (some : checkOrPanic p loc msg = some u) : p := by
  grind [checkOrPanic]

@[grind .]
theorem checkOrPanic_none {p : Prop} [Decidable p] {loc msg : String}
    (none : checkOrPanic p loc msg = none) : ¬p := by
  grind [checkOrPanic]

end Valaig
