module

public import Std.Sat.AIG.Basic
public import Std.Sat.AIG.CachedGates
public meta import Valaig.Prelude
public import Valaig.Aig.StdSatLemmas
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

-- Switch to public
public section
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
@[inline]
def empty : Aig :=
  {
    aig := .empty,
    inputs := #[],
    latches := #[],
  }

/--
The number of nodes currently allocated in aig.
-/
@[inline, local grind, local grind unfold]
def size (aig : Aig) : Nat :=
  aig.aig.decls.size

/--
The maximum variable currently allocated in the aig.
-/
@[inline]
def maxVar (aig : Aig) : Var :=
  .ofIdx <| aig.size - 1

/--
The number of input nodes in the aig.
-/
@[inline]
def numInputs (aig : Aig) : Nat :=
  aig.inputs.size

/--
The number of latch nodes in the aig.
-/
@[inline]
def numLatches (aig : Aig) : Nat :=
  aig.latches.size

/--
The number of gate nodes in the aig.
-/
@[inline, local simp, local grind unfold]
abbrev numGates (aig : Aig) : Nat :=
  aig.size - aig.numInputs - aig.numLatches - 1

end Aig

/-
Variable accessors.
-/

namespace Var 

def validIn (var : Var) (aig : Aig) : Prop :=
  var.idx < aig.size

@[inline]
instance {var : Var} {aig : Aig} : Decidable (var.validIn aig) :=
  have : var.validIn aig ↔ var.idx < aig.size := by
    simp [Var.validIn]
  decidable_of_iff' _ this

end Var

namespace Lit

@[expose, reducible, simp, grind unfold]
def validIn (lit : Lit) (aig : Aig) : Prop :=
  lit.var.validIn aig

@[inline]
instance {lit : Lit} {aig : Aig} : Decidable (lit.validIn aig) :=
  have : lit.validIn aig ↔ lit.var.validIn aig := by
    simp [Lit.validIn]
  decidable_of_iff' _ this

end Lit

@[always_inline]
def Aig.get (aig : Aig) (var : Var) (valid : var.validIn aig := by grind) : Node :=
  match aig.aig.decls[var.idx] with
  | .false => .false
  | .atom (.input idx) => .input idx
  | .atom (.latch idx) => .latch idx
  | .gate rhs0 rhs1 => .and (.ofFanin rhs0) (.ofFanin rhs1)

@[inline, expose, reducible, simp, grind unfold]
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

@[inline, simp]
abbrev InputIdx.getLit (idx : Aig.InputIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Lit :=
  idx.getVar aig valid |>.toLit

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

@[inline, simp]
abbrev LatchIdx.getLit (idx : Aig.LatchIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Lit :=
  idx.getVar aig valid |>.toLit

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

/--
Arbitrary index validity and accessors, defined as abbreviations
-/

@[simp]
abbrev AtomIdx.validIn (idx : Aig.AtomIdx) (aig : Aig) : Prop :=
  match idx with
  | .input idx => idx.validIn aig
  | .latch idx => idx.validIn aig

@[simp]
abbrev AtomIdx.getVar (idx : Aig.AtomIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Var :=
  match idx with
  | .input idx => idx.getVar aig
  | .latch idx => idx.getVar aig

@[simp]
abbrev AtomIdx.getLit (idx : Aig.AtomIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Lit :=
  match idx with
  | .input idx => idx.getLit aig
  | .latch idx => idx.getLit aig

instance : Coe InputIdx AtomIdx where
  coe := (.input ·)

instance : Coe LatchIdx AtomIdx where
  coe := (.latch ·)

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

/-
Setup get/set definitions for use locally as grind/simp rules, with grind_def/
simp_def tactics to make use of them.
-/
attribute [simp_valaig_defs, grind_valaig_defs]
  Aig.get Aig.instGetElemVar Aig.size
  Aig.empty
  InputIdx.getVar
  LatchIdx.getVar LatchIdx.getNext LatchIdx.getReset
  LatchIdx.setNext LatchIdx.setReset
  Aig.addInput Aig.addLatch Aig.addAnd

attribute [grind_valaig_defs] InputIdx LatchIdx
attribute [grind_valaig_defs =_] Var.ext_idx

attribute [simp_valaig_defs, grind_valaig_defs =]
  Std.mkAtom_eq_decls_push Std.mkAtom_size Std.mkAtom_ref_eq_decls_size
  Std.Sat.AIG.mkAndCached_decl_eq

attribute [grind_valaig_defs! .] Std.Sat.AIG.mkAndCached_le_size
