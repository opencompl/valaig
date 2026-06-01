module

public section
namespace Valaig.Data

/--
  Nullable represents types with encoding space carved out to represent null values. This allows
  a generalization of `Option α` to equivalents that pack the none value into unused encoding
  space, which can be more memory efficient.

  `null` specifies one null value to allow their construction, and `isNull` defines the space
  of null values, which must include `null`.
-/
class Nullable (α : Type u) where
  null : α
  isNull : α -> Bool
  legal : isNull null

namespace Nullable
variable {α : Type u} [inst : Nullable α]

@[simp, grind =]
theorem isNull_null :
    inst.isNull inst.null :=
  inst.legal

@[inline]
def isSome (a : α) :=
  !inst.isNull a

@[simp, grind =]
theorem isSome_eq {a : α} :
    inst.isSome a = !inst.isNull a := by
  rfl

@[inline]
instance : Nullable (Option α) where
  null := none
  isNull := Option.isNone
  legal := by grind

end Nullable
