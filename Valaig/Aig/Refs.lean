import Std.Sat.AIG.Basic

namespace Valaig

/--
Variable: a reference to a node in an Aig based on its index
-/
structure Var where
  ofIdx ::
    idx : Nat
deriving Hashable, DecidableEq, Repr, Inhabited, Ord, BEq, ReflBEq, LawfulBEq

namespace Var

instance : LE Var := leOfOrd
instance : LT Var := ltOfOrd
instance : Min Var := minOfLe
instance : Max Var := maxOfLe

@[inline]
def constant : Var :=
  .ofIdx 0

@[inline]
def offset (v : Var) (n : Nat) : Var :=
  .ofIdx <| (v.idx + n)

@[inline]
def next (v : Var) : Var :=
  v.offset 1

@[inline]
def ofRef {α} [DecidableEq α] [Hashable α] {aig : Std.Sat.AIG α} (ref : aig.Ref) : Var :=
  .ofIdx ref.gate

end Var

/--
Literal: a reference to a variable in an Aig and an inversion
-/
structure Lit where
  ofIdx ::
    idx : Nat
deriving Hashable, DecidableEq, Repr, Inhabited, BEq, ReflBEq, LawfulBEq

namespace Lit

@[inline]
def mk (v : Var) (invert : Bool := false) : Lit :=
  .ofIdx <| v.idx * 2 ||| invert.toNat

@[inline]
def var (l : Lit) : Var :=
  .ofIdx <| l.idx / 2

@[inline]
def inverted (l : Lit) : Prop :=
  (l.idx &&& 1) ≠ 0
deriving Decidable

@[inline]
def constant (value : Bool) : Lit :=
  mk .constant value

@[inline]
def false : Lit :=
  constant .false

@[inline]
def true : Lit :=
  constant .true

@[inline]
def isConstant (l : Lit) : Prop :=
  l.var = .constant
deriving Decidable

@[inline]
def isFalse (l : Lit) : Prop :=
  l = false
deriving Decidable

@[inline]
def isTrue (l : Lit) : Prop :=
  l = true
deriving Decidable

@[always_inline]
def invert (l : Lit) (doInvert : Bool := .true) : Lit :=
  if doInvert then
    .ofIdx <| l.idx ^^^ 1
  else
    l

-- Clear inverted
@[inline]
def strip (l : Lit) : Lit :=
  .ofIdx <| l.idx ^^^ (l.idx &&& 1)

@[inline]
def ofFanin (fi : Std.Sat.AIG.Fanin) : Lit :=
  mk (.ofIdx fi.gate) fi.invert

section
variable {α} [DecidableEq α] [Hashable α] {aig : Std.Sat.AIG α}

@[inline]
def ofRef (ref : aig.Ref) : Lit :=
  mk (.ofRef ref) ref.invert

@[inline]
def toRef (lit : Lit) (h : lit.var.idx < aig.decls.size) : aig.Ref :=
  .mk lit.var.idx lit.inverted h

end

end Lit

namespace Var

@[inline, simp]
abbrev toLit (v : Var) (invert : Bool := false) : Lit :=
  .mk v invert

end Var

end Valaig
