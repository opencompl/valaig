module

public import Std.Sat.AIG.Basic
public import Std.Sat.AIG.CachedGates
public import Valaig.Aig.Refs
public import Valaig.ForStd

namespace Valaig.Aig

/--
The metadata of an input in the Aig.
-/
structure Input where
  var : Var

namespace Input
deriving instance Hashable, DecidableEq, Repr, Inhabited for Input
end Input

/--
The metadata of a latch in the Aig.
-/
structure Latch where
  var : Var
  next : Lit
  reset : Lit

namespace Latch
deriving instance Hashable, DecidableEq, Repr, Inhabited for Latch
end Latch

abbrev Inputs := Array Input
abbrev Latches := Array Latch

end Valaig.Aig
public section pub
namespace Valaig.Aig

/--
An index to an input definition in the Aig input array.
-/
structure InputIdx where
  ofIdx ::
    idx : Nat

namespace InputIdx
deriving instance DecidableEq, Repr, Inhabited, BEq, ReflBEq, LawfulBEq for InputIdx
instance : Hashable InputIdx where hash := (hash ·.idx)
instance : LawfulHashable InputIdx where hash_eq := by simp
end InputIdx

/--
An index to a latch definition in the Aig latch array.
-/
structure LatchIdx where
  ofIdx ::
    idx : Nat

namespace LatchIdx
deriving instance DecidableEq, Repr, Inhabited, BEq, ReflBEq, LawfulBEq for LatchIdx
instance : Hashable LatchIdx where hash := (hash ·.idx)
instance : LawfulHashable LatchIdx where hash_eq := by simp
end LatchIdx

/--
An atom in the combinational aig is either an input or a latch, which is just
a reference back to the index in the inputs or latches arrays.
-/
inductive AtomIdx where
| input (idx : InputIdx)
| latch (idx : LatchIdx)

namespace AtomIdx
deriving instance Hashable, DecidableEq, Repr, Inhabited, BEq, ReflBEq, LawfulBEq for AtomIdx
instance : LawfulHashable AtomIdx where hash_eq := by simp
end AtomIdx

/--
An output of interest in the circuit - this is also used to represent other
nameable nodes in the Aiger format like bad and constraint nodes.
-/
structure Output where
  lit : Lit

namespace Output
deriving instance Hashable, DecidableEq, Repr, Inhabited for Output
end Output

abbrev Outputs := Array Output

end Aig

/--
A sequential And-Inverter Graph consisting of inputs, latches and And gates. Outputs should be
stored separately as `Lit`s in the `Aig`.
-/
structure Aig where
  -- The underlying AIG
  private aig : Std.Sat.AIG Aig.AtomIdx

  -- A mapping from input indices (AtomIdx.input idx) to their definition
  private inputs : Aig.Inputs

  -- A mapping from latch indices (AtomIdx.latch idx) to their definition
  private latches : Aig.Latches

namespace Aig

/--
A representation of the node data stored for a particular variable in an `Aig`. For inputs and
latches this requires a further lookup with `InputIdx.get` or `LatchIdx.get`.
-/
inductive Node where
  | false
  | input (idx : InputIdx)
  | latch (idx : LatchIdx)
  | and (lhs rhs : Lit)

namespace Node
deriving instance Hashable, DecidableEq, Repr, Inhabited for Node
end Node

/--
An `Aig` with just the constant node.
-/
def empty : Aig :=
  {
    aig := .empty,
    inputs := #[],
    latches := #[],
  }

/--
The number of nodes currently allocated in aig.
-/
@[local grind]
def size (aig : Aig) : Nat :=
  aig.aig.decls.size

end Aig

/-
Variable accessors.
-/

def Var.validIn (var : Var) (aig : Aig) : Prop :=
  var.idx < aig.size
deriving Decidable

def Lit.validIn (lit : Lit) (aig : Aig) : Prop :=
  lit.var.validIn aig
deriving Decidable

@[always_inline]
def Aig.get (aig : Aig) (var : Var) (valid : var.validIn aig := by grind) : Node :=
  match aig.aig.decls[var.idx] with
  | .false => .false
  | .atom (.input idx) => .input idx
  | .atom (.latch idx) => .latch idx
  | .gate rhs0 rhs1 => .and (.ofFanin rhs0) (.ofFanin rhs1)

@[inline]
instance Aig.instGetElemVar : GetElem Aig Var Node (fun aig var => var.validIn aig) where
  getElem aig var (h := by grind) :=
    aig.get var h

namespace Aig

/-
Input accessors.
-/

@[local simp]
def InputIdx.validIn (idx : Aig.InputIdx) (aig : Aig) : Prop :=
  idx.idx < aig.inputs.size
deriving Decidable

@[inline]
def InputIdx.getVar (idx : Aig.InputIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Var :=
  aig.inputs[idx.idx].var

@[inline]
def InputIdx.setVar (idx : Aig.InputIdx) (aig : Aig) (var : Var) (valid : idx.validIn aig := by grind) : Aig :=
  { aig with inputs := aig.inputs.modifyMem idx.idx (by simp_all) ({ ·.val with var }) }

/-
Latch accessors.
-/

@[local simp]
def LatchIdx.validIn (idx : Aig.LatchIdx) (aig : Aig) : Prop :=
  idx.idx < aig.latches.size
deriving Decidable

@[inline]
def LatchIdx.getVar (idx : Aig.LatchIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Var :=
  aig.latches[idx.idx].var

@[inline]
def LatchIdx.setVar (idx : Aig.LatchIdx) (aig : Aig) (var : Var) (valid : idx.validIn aig := by grind) : Aig :=
  { aig with latches := aig.latches.modifyMem idx.idx (by simp_all) ({ ·.val with var }) }

@[inline]
def LatchIdx.getNext (idx : Aig.LatchIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Lit :=
  aig.latches[idx.idx].next

@[inline]
def LatchIdx.setNext (idx : Aig.LatchIdx) (aig : Aig) (next : Lit) (valid : idx.validIn aig := by grind) : Aig :=
  { aig with latches := aig.latches.modifyMem idx.idx (by simp_all) ({ ·.val with next }) }

@[inline]
def LatchIdx.getReset (idx : Aig.LatchIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Lit :=
  aig.latches[idx.idx].reset

@[inline]
def LatchIdx.setReset (idx : Aig.LatchIdx) (aig : Aig) (reset : Lit) (valid : idx.validIn aig := by grind) : Aig :=
  { aig with latches := aig.latches.modifyMem idx.idx (by simp_all) ({ ·.val with reset }) }

/-
Generic index type that can be Var, InputIdx or LatchIdx used for proof reasoning, particularly
when operations invalidate no indices.
-/

inductive GenericIdx where
| node (var : Var)
| input (idx : InputIdx)
| latch (idx : LatchIdx)

def GenericIdx.validIn (idx : GenericIdx) (aig : Aig) : Prop :=
  match idx with
  | node var => var.validIn aig
  | input idx => idx.validIn aig
  | latch idx => idx.validIn aig

namespace GenericIdx
variable {aig : Aig}

/-
Lemmas to convert between specific and generic index forms.
-/
@[simp, grind =, grind =_] theorem iff_node (var : Var) : (node var).validIn aig ↔ var.validIn aig := by rfl
@[simp, grind =, grind =_] theorem iff_input (idx : InputIdx) : (input idx).validIn aig ↔ idx.validIn aig := by rfl
@[simp, grind =, grind =_] theorem iff_latch (idx : LatchIdx) : (latch idx).validIn aig ↔ idx.validIn aig := by rfl

end GenericIdx

/-
Node constructors. There is no constant node constructor as the constant node always exists, so constant
literals can be constructed with `Lit.true`/`Lit.false`.
-/

@[inline]
def addInput (aig : Aig) : Aig × InputIdx :=
  let idx := .ofIdx aig.inputs.size
  let res := aig.aig.mkAtom <| .input idx
  let input := { var := .ofRef res.ref }
  let inputs := aig.inputs.push input
  let aig := { aig with aig := res.aig, inputs }
  (aig, idx)

@[inline]
def addLatch (aig : Aig) (next reset : Lit) : Aig × LatchIdx :=
  let idx := .ofIdx aig.latches.size
  let res := aig.aig.mkAtom <| .latch idx
  let latch := { var := .ofRef res.ref, next, reset }
  let latches := aig.latches.push latch
  let aig := { aig with aig := res.aig, latches }
  (aig, idx)

-- TODO: Currently this requires proofs that rhs0/rhs1 are valid in the aig, but after switching to
-- buffed (and getting rid of dependent typing) this won't be needed anymore
@[inline]
def addAnd (aig : Aig) (rhs0 rhs1 : Lit)
    (valid0 : rhs0.validIn aig := by grind) (valid1 : rhs1.validIn aig := by grind) : Aig × Lit :=
  let res := aig.aig.mkAndCached ⟨rhs0.toRef valid0, rhs1.toRef valid1⟩
  let aig := { aig with aig := res.aig }
  (aig, .ofRef res.ref)

end Valaig.Aig
end pub
