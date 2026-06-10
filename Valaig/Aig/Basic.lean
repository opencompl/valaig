module

public import Valaig.Aig.NodeArray
import Valaig.Aig.TwoLevelSimp
public import Valaig.Data.Pool
public import Valaig.Data.AbsMap
public import Valaig.Refs
import Valaig.ForLean.Iter
public import Valaig.ForLean.Panic

public section
open Valaig.Data (AbsMap Pool)

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
  We require the inputs we store in the array to only track non-constant indices.

  NOTE: Users should not rely on this type, it may change!
-/
abbrev InputData := { input : Input // input.var ≠ .constant }

namespace InputData

@[inline]
instance : Inhabited InputData where
  default := ⟨{ var := Var.constant + 1 }, by grind⟩

end InputData

/--
  The metadata of a latch in the Aig.
-/
structure Latch where
  var : Var
  next : Lit
  reset : Option Lit

namespace Latch
deriving instance Hashable, DecidableEq, Repr, Inhabited for Latch
end Latch

/--
  We require the inputs we store in the array to only track non-constant indices.

  NOTE: Users should not rely on this type, it may change!
-/
abbrev LatchData := { latch : Latch // latch.var ≠ .constant }

namespace LatchData

@[inline]
instance : Inhabited LatchData where
  default := ⟨{ var := Var.constant + 1, next := .false, reset := none }, by grind⟩

end LatchData

end Valaig.Aig

namespace Valaig.Aig

/--
  An index to an input definition in the Aig. These inputs are primary inputs (PIs).
-/
@[ext, grind ext]
structure InputIdx where
  ofIdx ::
    idx : Nat

namespace InputIdx
deriving instance DecidableEq, Repr, Inhabited, BEq, ReflBEq, LawfulBEq for InputIdx
instance : Hashable InputIdx where hash := (hash ·.idx)
instance : LawfulHashable InputIdx where hash_eq := by simp
end InputIdx

/--
  An index to a latch definition in the Aig.
-/
@[ext, grind ext]
structure LatchIdx where
  ofIdx ::
    idx : Nat

namespace LatchIdx
deriving instance DecidableEq, Repr, Inhabited, BEq, ReflBEq, LawfulBEq for LatchIdx
instance : Hashable LatchIdx where hash := (hash ·.idx)
instance : LawfulHashable LatchIdx where hash_eq := by simp
end LatchIdx

/--
  A leaf in the Aig is either an input or a latch, which is a reference back to the index
  in the inputs or latches.
  These are what abc calls Combinational Inputs (CIs).
-/
inductive LeafIdx where
| input (idx : InputIdx)
| latch (idx : LatchIdx)

namespace LeafIdx
deriving instance Hashable, DecidableEq, Repr, Inhabited, BEq, ReflBEq, LawfulBEq for LeafIdx
instance : LawfulHashable LeafIdx where hash_eq := by simp

@[always_inline]
instance : Coe InputIdx LeafIdx where
  coe := (.input ·)

@[always_inline]
instance : Coe LatchIdx LeafIdx where
  coe := (.latch ·)

end LeafIdx

/--
  A representation of the node data stored for a particular variable in an `Aig`. For inputs and
  latches this requires a further lookup with `InputIdx.get` or `LatchIdx.get`.
-/
inductive Node where
  | false
  | input (idx : InputIdx)
  | latch (idx : LatchIdx)
  | and (lhs rhs : Lit)

@[always_inline]
instance : Coe InputIdx Node where
  coe := (.input ·)

@[always_inline]
instance : Coe LatchIdx Node where
  coe := (.latch ·)

@[always_inline]
instance : Coe LeafIdx Node where
  coe
  | .input idx
  | .latch idx => idx

namespace Node
deriving instance Hashable, DecidableEq, Repr, Inhabited for Node
end Node

/--
  The generic representation of nodes in the Aig, including inputs, latches and
  gates. These are interpreted relative to their position in the Aig to give
  semantics, see `NodeData.toNode`.

  NOTE: Users should not rely on this type, it may change!
-/
abbrev NodeData := Lit × Lit

namespace NodeData

private def false : NodeData :=
  (.false, .false)

@[always_inline, local simp, local grind]
private def input (idx : InputIdx) (var : Var) : NodeData :=
  (var.toLit .false, .ofIdx idx.idx)

@[always_inline, local simp, local grind]
private def latch (idx : LatchIdx) (var : Var) : NodeData :=
  (var.toLit .true, .ofIdx idx.idx)

@[always_inline, local simp, local grind]
private def and (lhs rhs : Lit) : NodeData :=
  (lhs, rhs)

@[always_inline, local simp, local grind]
private def toNode (data : NodeData) (var : Var) : Node :=
  if var = .constant then
    .false
  else if data.fst.var = var then
    if !data.fst.inverted then
      .input <| .ofIdx data.snd.idx
    else
      .latch <| .ofIdx data.snd.idx
  else
    .and data.fst data.snd

@[simp, grind =]
private theorem toNode_constant {data : NodeData} :
    data.toNode .constant = .false := by
  simp

@[simp, grind =]
private theorem toNode_input {idx : InputIdx} {var : Var} (notConst : var ≠ .constant) :
    (input idx var).toNode var = idx := by
  grind

@[simp, grind =]
private theorem toNode_latch {idx : LatchIdx} {var : Var} (notConst : var ≠ .constant) :
    (latch idx var).toNode var = idx := by
  grind

set_option linter.unusedVariables false in
@[simp, grind =]
private theorem toNode_and {lhs rhs : Lit} {var : Var} (notConst : var ≠ .constant)
    (h0 : lhs.var ≠ var) (h1 : rhs.var ≠ var) :
    (and lhs rhs).toNode var = .and lhs rhs := by
  grind

end NodeData

end Aig

/--
  A sequential And-Inverter Graph consisting of inputs, latches and And gates.
-/
structure Aig where
  /-- The core array of nodes making up the Aig. -/
  private _nodes : Aig.NodeArray

  /-- A mapping from input indices (`InputIdx`) to their definition. -/
  _inputs : Pool Aig.InputData

  /-- A mapping from latch indices (`LatchIdx`) to their definition. -/
  _latches : Pool Aig.LatchData

variable {aig : Aig}

namespace Aig

@[always_inline]
instance : AbsMap.AsNat Var where
  toNat := Var.idx
  ofNat := Var.ofIdx

/--
  An abstract representation of the mapping from variables to the corresponding node in the Aig.
  This allows an abstract representation of variable validity (`var ∈ aig.nodes`),
  lookup (`aig.nodes[var]`) and size (`aig.nodes.size`).

  NOTE: This should not be used in computation, instead preferring `var.validIn aig`, `aig[var]`
  and `aig.size`.
-/
@[always_inline]
def nodes (aig : Aig) : AbsMap Var Node :=
  .mk
    (valid := (· ∈ aig._nodes))
    (map := fun var valid => NodeData.toNode aig._nodes[var] var)
    (size := aig._nodes.size)

@[always_inline]
instance : AbsMap.AsNat InputIdx where
  toNat := InputIdx.idx
  ofNat := InputIdx.ofIdx

/--
  An abstract representation of the mapping from `InputIdx`s to the corresponding input in the Aig.
  This allows an abstract representation of index validity (`idx ∈ aig.inputs`),
  lookup (`aig.inputs[idx]`) and size (`aig.inputs.size`).

  NOTE: This should not be used in computation, instead preferring `idx.validIn aig`,
  `idx.getVar aig` and `aig.numInputs`.
-/
@[always_inline]
def inputs (aig : Aig) : AbsMap InputIdx Input :=
  AbsMap.ofPool aig._inputs InputIdx |>.mapVal (·.val)

@[always_inline]
instance : AbsMap.AsNat LatchIdx where
  toNat := LatchIdx.idx
  ofNat := LatchIdx.ofIdx

/--
  An abstract representation of the mapping from `LatchIdx`s to the corresponding latch in the Aig.
  This allows an abstract representation of index validity (`idx ∈ aig.latches`),
  lookup (`aig.latches[idx]`) and size (`aig.latches.size`).

  NOTE: This should not be used in computation, instead preferring `idx.validIn aig`,
  `idx.getVar aig`/`idx.getNext aig`/`idx.getReset aig` and `aig.numLatches`.
-/
@[always_inline]
def latches (aig : Aig) : AbsMap LatchIdx Latch :=
  AbsMap.ofPool aig._latches LatchIdx |>.mapVal (·.val)

/--
  A pair of Aigs are monotone (represented with `old ≤ new`) if all references valid in the old Aig
  are also valid in the new Aig and all getters for these references return the same values.
-/
structure Monotone (old new : Aig) : Prop where
  nodes : old.nodes ≤ new.nodes
  inputs : old.inputs ≤ new.inputs
  latches : old.latches ≤ new.latches

@[inherit_doc Monotone]
instance : LE Aig where
  le := Monotone

/--
  The number of nodes currently allocated in the Aig.
  This includes both And gates as well as inputs and latches.
-/
@[always_inline]
def size (aig : Aig) : Nat :=
  aig._nodes.size

/--
  The number of inputs in the Aig.
-/
@[always_inline]
def numInputs (aig : Aig) : Nat :=
  aig._inputs.size

/--
  The number of latches in the Aig.
-/
@[always_inline]
def numLatches (aig : Aig) : Nat :=
  aig._latches.size

/--
  The number of and gate nodes in the Aig.
-/
abbrev numGates (aig : Aig) : Nat :=
  aig.size - aig.numInputs - aig.numLatches - 1

/--
  The variable with the highest index currently allocated in the Aig.
  All variables up to this variable are also allocated.
-/
@[always_inline]
def maxVar (aig : Aig) : Var :=
  .ofIdx <| aig.size - 1

/--
  The smallest variable not currently allocated in the Aig.
  This is the variable that is allocated for methods that append a node.
-/
@[always_inline]
def nextVar (aig : Aig) : Var :=
  .ofIdx <| aig.size

@[simp, grind .]
theorem not_constant_next_var :
    aig.nextVar ≠ .constant := by
  grind [nextVar, size]

/--
  The (arbitrary) next input index not currently allocated in the Aig.
  This is the index that is allocated for methods that append an input.
-/
@[always_inline]
def newInputIdx (aig : Aig) : InputIdx :=
  .ofIdx aig._inputs.nextIdx

/--
  The (arbitrary) next latch index not currently allocated in the Aig.
  This is the index that is allocated for methods that append a latch.
-/
@[always_inline]
def newLatchIdx (aig : Aig) : LatchIdx :=
  .ofIdx aig._latches.nextIdx

end Aig

/-
  Validity predicates.
-/
namespace Var 

/--
  A variable is `validIn` an Aig iff it has a node defined for it.
-/
@[expose]
def validIn (var : Var) (aig : Aig) : Prop :=
  var ∈ aig.nodes

/-- NOTE: Do not rely on this function externally! -/
@[always_inline]
def instDecidableValidIn.impl (var : Var) (aig : Aig) : Bool :=
  var ∈ aig._nodes

@[always_inline]
instance {var : Var} : Decidable (var.validIn aig) :=
  have : var.validIn aig ↔ instDecidableValidIn.impl var aig := by
    simp [instDecidableValidIn.impl, validIn, Aig.nodes]
  decidable_of_iff' _ this

/--
  A dependently type variable that is known to be valid in a given Aig.
  This allows packing the proof of validity together with the variable.
-/
abbrev In (aig : Aig) := { var : Var // var.validIn aig }

/--
  Cast a `Var` into a `Var.In aig`. This tries to use `grind` to prove that the variable is
  valid in the Aig.
-/
@[always_inline, simp]
abbrev castIn (var : Var) (aig : Aig) (valid : var.validIn aig := by grind) : Var.In aig :=
  ⟨var, valid⟩

end Var

namespace Lit

/--
  A literal is `validIn` an Aig iff its variable is also.
-/
@[always_inline, reducible, expose, simp, grind unfold]
def validIn (lit : Lit) (aig : Aig) : Prop :=
  lit.var.validIn aig

@[always_inline]
instance {lit : Lit} {aig : Aig} : Decidable (lit.validIn aig) :=
  have : lit.validIn aig ↔ lit.var.validIn aig := by simp
  decidable_of_iff' _ this

/--
  A dependently type literal that is known to be valid in a given Aig.
  This allows packing the proof of validity together with the literal.
-/
abbrev In (aig : Aig) := { lit : Lit // lit.validIn aig }

/--
  Cast a `Lit` into a `Lit.In aig`. This tries to use `grind` to prove that the literal is
  valid in the Aig.
-/
@[always_inline, simp]
abbrev castIn (lit : Lit) (aig : Aig) (valid : lit.validIn aig := by grind) : Lit.In aig :=
  ⟨lit, valid⟩

end Lit

namespace Aig

namespace InputIdx

/--
  An input is `validIn` an Aig iff it is a member of `aig.inputs`.
-/
@[expose]
def validIn (idx : InputIdx) (aig : Aig) : Prop :=
  idx ∈ aig.inputs

/-- NOTE: Do not rely on this function externally! -/
@[always_inline]
def instDecidableValidIn.impl (idx : InputIdx) (aig : Aig) : Bool :=
  idx.idx ∈ aig._inputs

private theorem validIn_def {idx : InputIdx} :
    idx.validIn aig ↔ idx.idx ∈ aig._inputs := by
  simp [validIn, inputs]

@[always_inline]
instance {idx : InputIdx} : Decidable (idx.validIn aig) :=
  have : idx.validIn aig ↔ instDecidableValidIn.impl idx aig := by simp [instDecidableValidIn.impl, validIn_def]
  decidable_of_iff' _ this

/--
  A dependently type `InputIdx` that is known to be valid in a given Aig.
  This allows packing the proof of validity together with the index.
-/
abbrev In (aig : Aig) := { idx : InputIdx // idx.validIn aig }

/--
  Cast an `InputIdx` into an `InputIdx.In aig`. This tries to use `grind` to prove that the index is
  valid in the Aig.
-/
@[always_inline, simp]
abbrev castIn (idx : InputIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : InputIdx.In aig :=
  ⟨idx, valid⟩

end InputIdx

namespace LatchIdx

/--
  A latch is `validIn` an Aig iff it is a member of `aig.latches`.
-/
@[expose]
def validIn (idx : LatchIdx) (aig : Aig) : Prop :=
  idx ∈ aig.latches

/-- NOTE: Do not rely on this function externally! -/
@[always_inline]
def instDecidableValidIn.impl (idx : LatchIdx) (aig : Aig) : Bool :=
  idx.idx ∈ aig._latches

private theorem validIn_def {idx : LatchIdx} :
    idx.validIn aig ↔ idx.idx ∈ aig._latches := by
  simp [validIn, latches]

@[always_inline]
instance {idx : LatchIdx} : Decidable (idx.validIn aig) :=
  have : idx.validIn aig ↔ instDecidableValidIn.impl idx aig := by simp [instDecidableValidIn.impl, validIn_def]
  decidable_of_iff' _ this

/--
  A dependently type `LatchIdx` that is known to be valid in a given Aig.
  This allows packing the proof of validity together with the index.
-/
abbrev In (aig : Aig) := { idx : LatchIdx // idx.validIn aig }

/--
  Cast an `LatchIdx` into an `LatchIdx.In aig`. This tries to use `grind` to prove that the index is
  valid in the Aig.
-/
@[always_inline, simp]
abbrev castIn (idx : LatchIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : LatchIdx.In aig :=
  ⟨idx, valid⟩

end LatchIdx

attribute [local simp, local grind =] InputIdx.validIn_def LatchIdx.validIn_def

/-- NOTE: Do not rely on this function externally! -/
@[always_inline]
def instGetElemVar.impl (aig : Aig) (var : Var) (valid : var.validIn aig := by grind) : Node :=
  NodeData.toNode aig._nodes[var] var

@[always_inline]
instance instGetElemVar : GetElem Aig Var Node (fun aig var => var.validIn aig) where
  getElem aig var h :=
    instGetElemVar.impl aig var h

private theorem getElem_eq' {var : Var} {valid : var.validIn aig} :
    aig[var]'valid = NodeData.toNode aig._nodes[var] var := by
  simp [instGetElemVar, instGetElemVar.impl]

/--
  An Aig with just the constant node.
-/
def empty : Aig where
  _nodes := .empty
  _inputs := .empty
  _latches := .empty

@[inline]
instance : Inhabited Aig where
  default := empty

/-
  Input accessors.
-/
namespace InputIdx

/--
  Lookup the variable (PI) defined by this input in the Aig.
-/
@[inline]
def getVar (idx : InputIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Var :=
  aig._inputs[idx.idx].val.var

/--
  Lookup the variable (PI) defined by this input in the Aig.

  Panics and returns none if `idx` isn't valid in the Aig.
  Otherwise returns `idx.getVar aig`.
-/
@[always_inline]
def getVar! (idx : InputIdx) (aig : Aig) : Option Var :=
  match aig._inputs[idx.idx]? with
  | none       => panicAt "Valaig.Aig.InputIdx.getVar!" "`idx` not valid in `aig`"
  | some input => input.val.var

/--
  Lookup the variable defined by this input in the Aig and cast it to an uninverted literal.
-/
@[inline]
def getLit (idx : InputIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Lit :=
  idx.getVar aig valid |>.toLit

/--
  Lookup the variable defined by this input in the Aig and cast it to an uninverted literal.

  If `idx` isn't valid in the Aig, throws `err`.
-/
@[always_inline]
def getLit! (idx : InputIdx) (aig : Aig) : Option Lit :=
  match aig._inputs[idx.idx]? with
  | none       => panicAt "Valaig.Aig.InputIdx.getLit!" "`idx` not valid in `aig`"
  | some input => input.val.var.toLit

end InputIdx

/-
  Latch accessors.
-/
namespace LatchIdx

/--
  Lookup the variable (CI) defined by this latch in the Aig.
-/
@[inline]
def getVar (idx : LatchIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Var :=
  aig._latches[idx.idx].val.var

/--
  Lookup the variable (CI) defined by this latch in the Aig.

  If `idx` isn't valid in the Aig, throws `err`.
-/
@[always_inline]
def getVar! (idx : LatchIdx) (aig : Aig) : Option Var :=
  match aig._latches[idx.idx]? with
  | none       => panicAt "Valaig.Aig.LatchIdx.getVar!" "`idx` not valid in `aig`"
  | some latch => latch.val.var

/--
  Lookup the variable defined by this latch in the Aig and cast it to an uninverted literal.
-/
@[inline]
def getLit (idx : LatchIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Lit :=
  idx.getVar aig valid |>.toLit

/--
  Lookup the variable defined by this latch in the Aig and cast it to an uninverted literal.

  If `idx` isn't valid in the Aig, throws `err`.
-/
@[always_inline]
def getLit! (idx : LatchIdx) (aig : Aig) : Option Lit :=
  match aig._latches[idx.idx]? with
  | none       => panicAt "Valaig.Aig.LatchIdx.getLit!" "`idx` not valid in `aig`"
  | some latch => latch.val.var.toLit

/--
  Lookup the next state function defined for this latch in the Aig.
-/
@[inline]
def getNext (idx : LatchIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Lit :=
  aig._latches[idx.idx].val.next

/--
  Lookup the next state function defined for this latch in the Aig.

  If `idx` isn't valid in the Aig, throws `err`.
-/
@[always_inline]
def getNext! (idx : LatchIdx) (aig : Aig) : Option Lit :=
  match aig._latches[idx.idx]? with
  | none       => panicAt "Valaig.Aig.LatchIdx.getNext!" "`idx` not valid in `aig`"
  | some latch => latch.val.next

/--
  Lookup the optional reset function defined for this latch in the Aig.
-/
@[inline]
def getReset (idx : LatchIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Option Lit :=
  aig._latches[idx.idx].val.reset

/--
  Lookup the optional reset function defined for this latch in the Aig.

  If `idx` isn't valid in the Aig, throws `err`.
-/
@[always_inline]
def getReset! (idx : LatchIdx) (aig : Aig) : Option (Option Lit) :=
  match aig._latches[idx.idx]? with
  | none       => panicAt "Valaig.Aig.LatchIdx.getReset!" "`idx` not valid in `aig`"
  | some latch => return latch.val.reset


end LatchIdx

/--
  Update the next state function for a latch in the Aig.
-/
@[inline]
def setNext (aig : Aig) (idx : LatchIdx) (next : Lit) (valid : idx.validIn aig := by grind) : Aig :=
  { aig with _latches := aig._latches.modify idx.idx (⟨{ ·.val with next }, by grind⟩) }

/--
  Update the next state function for a latch in the Aig.

  If `idx` isn't valid in the Aig, throws `err`.
-/
@[always_inline]
def setNext! (aig : Aig) (idx : LatchIdx) (next : Lit) : Option Aig := do
  let h ← checkOrPanic (idx.validIn aig) "Valaig.Aig.setNext!" "`idx` not valid in `aig`"
  aig.setNext idx next

/--
  Update the reset function for a latch in the Aig.
-/
@[inline]
def setReset (aig : Aig) (idx : LatchIdx) (reset : Option Lit) (valid : idx.validIn aig := by grind) : Aig :=
  { aig with _latches := aig._latches.modify idx.idx (⟨{ ·.val with reset }, by grind⟩) }

/--
  Update the reset function for a latch in the Aig.

  If `idx` isn't valid in the Aig, throws `err`.
-/
@[always_inline]
def setReset! (aig : Aig) (idx : LatchIdx) (reset : Option Lit) : Option Aig := do
  let h ← checkOrPanic (idx.validIn aig) "Valaig.Aig.setReset!" "`idx` not valid in `aig`"
  aig.setReset idx reset

namespace LeafIdx

@[inline]
def asInput (idx : LeafIdx) (h : idx matches .input _ := by grind) : InputIdx :=
  match idx, h with
  | .input idx, _ => idx

@[inline]
def asLatch (idx : LeafIdx) (h : idx matches .latch _ := by grind) : LatchIdx :=
  match idx, h with
  | .latch idx, _ => idx

@[local grind]
def validIn (idx : LeafIdx) (aig : Aig) : Prop :=
  match idx with
  | .input idx
  | .latch idx => idx.validIn aig

instance {idx : InputIdx} : Coe (idx.validIn aig) ((idx : LeafIdx).validIn aig) where
  coe := by grind [validIn]

instance {idx : LatchIdx} : Coe (idx.validIn aig) ((idx : LeafIdx).validIn aig) where
  coe := by grind [validIn]

@[always_inline]
instance {idx : LeafIdx} {aig : Aig} : Decidable (idx.validIn aig) :=
  match h : idx with
  | .input idx
  | .latch idx =>
    decidable_of_bool (idx.validIn aig) (by grind)

abbrev In (aig : Aig) := { idx : LeafIdx // idx.validIn aig }

@[always_inline, simp]
abbrev castIn (idx : LeafIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : LeafIdx.In aig :=
  ⟨idx, valid⟩

@[always_inline]
instance : Coe (InputIdx.In aig) (LeafIdx.In aig) where
  coe idx := ⟨idx, idx.property⟩

@[always_inline]
instance : Coe (LatchIdx.In aig) (LeafIdx.In aig) where
  coe idx := ⟨idx, idx.property⟩

/--
  Lookup the variable(CI) defined by this leaf in the Aig.
-/
@[always_inline]
def getVar (idx : LeafIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Var :=
  match idx with
  | .input idx
  | .latch idx => idx.getVar aig

/--
  Lookup the variable (CI) defined by this leaf in the Aig.

  If `idx` isn't valid in the Aig, throws `err`.
-/
@[always_inline]
def getVar! (idx : LeafIdx) (aig : Aig) : Option Var :=
  match idx with
  | .input idx
  | .latch idx => idx.getVar! aig

/--
  Lookup the variable (CI) defined by this leaf in the Aig and cast it to an uninverted literal.
-/
@[always_inline]
def getLit (idx : LeafIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Lit :=
  idx.getVar aig valid |>.toLit

/--
  Lookup the variable (CI) defined by this leaf in the Aig and cast it to an uninverted literal.

  If `idx` isn't valid in the Aig, throws `err`.
-/
@[always_inline]
def getLit! (idx : LeafIdx) (aig : Aig) : Option Lit :=
  match idx with
  | .input idx
  | .latch idx => idx.getLit! aig

end LeafIdx

/--
  Push a new node onto the `Aig` from its data. This has the variable `aig.nextVar`.
-/
@[always_inline]
private def pushNode (aig : Aig) (node : NodeData) : Aig :=
  { aig with _nodes := aig._nodes.push node.fst node.snd }

/--
  Overwrite a node at a given index in the `Aig`.
  TODO: This currently breaks linearity, so the existing node data is dealloced and
  a new node alloced.
-/
@[always_inline]
private def setNode (aig : Aig) (var : Var) (node : NodeData) (valid : var.validIn aig := by grind) : Aig :=
  { aig with _nodes := aig._nodes.set var node.fst node.snd }

@[always_inline]
private def pushInput (aig : Aig) (input : Input) (h : input.var ≠ .constant := by grind) : Aig :=
  { aig with _inputs := aig._inputs.push ⟨input, h⟩ }

@[always_inline]
private def pushLatch (aig : Aig) (latch : Latch) (h : latch.var ≠ .constant := by grind) : Aig :=
  { aig with _latches := aig._latches.push ⟨latch, h⟩ }

@[always_inline]
private def eraseInput (aig : Aig) (idx : InputIdx) (valid : idx.validIn aig := by grind) : Aig :=
  { aig with _inputs := aig._inputs.erase idx.idx }

@[always_inline]
private def eraseLatch (aig : Aig) (idx : LatchIdx) (valid : idx.validIn aig := by grind) : Aig :=
  { aig with _latches := aig._latches.erase idx.idx }

@[always_inline]
private def moveInput (aig : Aig) (old new : InputIdx) (valid : old.validIn aig := by grind) (notvalid : ¬new.validIn aig ∨ new = old := by grind) : Aig :=
  { aig with _inputs := aig._inputs.move old.idx new.idx }

@[always_inline]
private def moveLatch (aig : Aig) (old new : LatchIdx) (valid : old.validIn aig := by grind) (notvalid : ¬new.validIn aig ∨ new = old := by grind) : Aig :=
  { aig with _latches := aig._latches.move old.idx new.idx }

attribute [local grind] InputIdx.validIn LatchIdx.validIn newInputIdx newLatchIdx

/--
  Append an input with a new index to the Aig, returning the index of the input.
-/
@[always_inline]
def addInput (aig : Aig) : Aig × InputIdx :=
  let idx := aig.newInputIdx
  let var := aig.nextVar
  let aig := aig.pushNode <| .input aig.newInputIdx var
  let aig := aig.pushInput { var }
  (aig, idx)

/--
  Append a latch with a new index to the Aig, returning the index of the latch.

  If `next` and `reset` are not known yet, they should be set to placeholders
  (like `Lit.false`/`Option.none`) and updated later with `LatchIdx.setNext`/`LatchIdx.setReset`.
-/
@[always_inline]
def addLatch (aig : Aig) (next : Lit) (reset : Option Lit := none) : Aig × LatchIdx :=
  let idx := aig.newLatchIdx
  let var := aig.nextVar
  let aig := aig.pushNode <| .latch idx var
  let aig := aig.pushLatch { var, next, reset }
  (aig, idx)

/--
  Append an and gate to the Aig, returning the variable defined by the new gate.
  This does not perform any optimizations.

  Note that neither input shuld be set to `nextVar` (equivalent to `Var.ofIdx aig.size`)
  or internal invariants are broken.
-/
@[always_inline]
def addAndRaw (aig : Aig) (lhs rhs : Lit) : Aig × Var :=
  let var := aig.nextVar
  let aig := aig.pushNode <| .and lhs rhs
  (aig, var)

/--
  Append an and gate to the Aig, returning the variable defined by the new gate.
  This performs the 2-level optimizations from `https://fmv.jku.at/papers/BrummayerBiere-MEMICS06.pdf`,
  but without structural hashing.

  Note that neither input shuld be set to `nextVar` (equivalent to `Var.ofIdx aig.size`)
  or internal invariants are broken.
-/
def addAnd (aig : Aig) (lhs rhs : Lit) : Aig × Lit :=
  -- TODO: This misses three-input rewrites that have a leaf anded with an and
  match aig[lhs.var]?, aig[rhs.var]? with
  | some (.and l0 l1), some (.and r0 r1) =>
    match TwoLevelSimp.simplifyAnd lhs rhs l0 l1 r0 r1 with
    | .lit l => (aig, l)
    | .and l r => let (aig, var) := aig.addAndRaw l r; (aig, var)
  | _, _ => let (aig, var) := aig.addAndRaw lhs rhs; (aig, var)

/--
  Convert an input into a new latch that defines the same variable, deleting the input.
-/
def inputToLatch (aig : Aig) (idx : InputIdx) (next : Lit) (reset : Option Lit := none)
    (valid : idx.validIn aig := by grind)
    (varValid : (idx.getVar aig).validIn aig := by grind) : Aig × LatchIdx :=
  let var := idx.getVar aig
  let latch := aig.newLatchIdx
  let aig := aig.setNode var <| .latch latch var
  let aig := aig.pushLatch { var, next, reset } (by grind [InputIdx.getVar])
  let aig := aig.eraseInput idx (by grind [pushLatch, setNode])
  (aig, latch)

/--
  Convert an input into a new latch that defines the same variable, deleting the input.

  If `idx` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `idx.getVar aig` is not valid in `aig`, throws `errVarInvalid`.
-/
@[always_inline]
def inputToLatch! (aig : Aig) (idx : InputIdx) (next : Lit) (reset : Option Lit := none) : Option (Aig × LatchIdx) := do
  let h ← checkOrPanic (idx.validIn aig)              "Valaig.Aig.inputToLatch!" "`idx` not valid in `aig`"
  let h ← checkOrPanic ((idx.getVar aig).validIn aig) "Valaig.Aig.inputToLatch!" "`idx.getVar aig` not valid in `aig`"
  aig.inputToLatch idx next reset

/--
  Convert an input into a new and gate that defines the same variable, deleting the input.
-/
@[inline]
def inputToAnd (aig : Aig) (idx : InputIdx) (lhs rhs : Lit)
    (valid : idx.validIn aig := by grind)
    (varValid : (idx.getVar aig).validIn aig := by grind) : Aig :=
  let var := idx.getVar aig
  let aig := aig.setNode var <| .and lhs rhs
  let aig := aig.eraseInput idx (by grind [setNode])
  aig

/--
  Convert an input into a new and gate that defines the same variable, deleting the input.

  If `idx` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `idx.getVar aig` is not valid in `aig`, throws `errVarInvalid`.
-/
@[always_inline]
def inputToAnd! (aig : Aig) (idx : InputIdx) (lhs rhs : Lit) : Option Aig := do
  let h ← checkOrPanic (idx.validIn aig)              "Valaig.Aig.inputToAnd!" "`idx` not valid in `aig`"
  let h ← checkOrPanic ((idx.getVar aig).validIn aig) "Valaig.Aig.inputToAnd!" "`idx.getVar aig` not valid in `aig`"
  aig.inputToAnd idx lhs rhs

/--
  Change the input index used to define an input to a new known unused one.
  This is mainly useful when trying to build a new Aig while preserving indices from an existing one.
-/
@[inline]
def changeInputIdx (aig : Aig) (old new : InputIdx)
    (valid : old.validIn aig := by grind)
    (varValid : (old.getVar aig).validIn aig := by grind)
    (unused : ¬new.validIn aig ∨ old = new := by grind) : Aig :=
  let data := aig._inputs[old.idx]
  let aig := aig.moveInput old new
  let aig := aig.setNode data.val.var (.input new data.val.var) (by grind [InputIdx.getVar, Var.validIn, moveInput, nodes])
  aig

/--
  Change the input index used to define an input to a new known unused one.
  This is mainly useful when trying to build a new Aig while preserving indices from an existing one.

  If `old` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `old.getVar aig` is not valid in `aig`, throws `errVarInvalid`.
  Otherwise if `new` is already valid in `aig` and not equal to `old`, throws `errUsed`.
-/
@[inline]
def changeInputIdx! (aig : Aig) (old new : InputIdx) : Option Aig := do
  let h ← checkOrPanic (old.validIn aig)              "Valaig.Aig.changeInputIdx!" "`old` not valid in `aig`"
  let h ← checkOrPanic ((old.getVar aig).validIn aig) "Valaig.Aig.changeInputIdx!" "`old.getVar aig` not valid in `aig`"
  let h ← checkOrPanic (¬new.validIn aig ∨ old = new) "Valaig.Aig.changeInputIdx!" "`new` already used in `aig`"
  aig.changeInputIdx old new

/--
  Convert a latch into a new input that defines the same variable, deleting the latch.
-/
def latchToInput (aig : Aig) (idx : LatchIdx)
    (valid : idx.validIn aig := by grind)
    (varValid : (idx.getVar aig).validIn aig := by grind) : Aig × InputIdx :=
  let var := idx.getVar aig
  let input := aig.newInputIdx
  let aig := aig.setNode var <| .input input var
  let aig := aig.pushInput { var } (by grind [LatchIdx.getVar])
  let aig := aig.eraseLatch idx (by grind [setNode, pushInput])
  (aig, input)

/--
  Convert a latch into a new input that defines the same variable, deleting the latch.

  If `idx` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `idx.getVar aig` is not valid in `aig`, throws `errVarInvalid`.
-/
@[always_inline]
def latchToInput! (aig : Aig) (idx : LatchIdx) : Option (Aig × InputIdx) := do
  let h ← checkOrPanic (idx.validIn aig)              "Valaig.Aig.latchToInput!" "`idx` not valid in `aig`"
  let h ← checkOrPanic ((idx.getVar aig).validIn aig) "Valaig.Aig.latchToInput!" "`idx.getVar aig` not valid in `aig`"
  aig.latchToInput idx

/--
  Convert a latch into a new and gate that defines the same variable, deleting the latch.
-/
@[inline]
def latchToAnd (aig : Aig) (idx : LatchIdx) (lhs rhs : Lit)
    (valid : idx.validIn aig := by grind)
    (varValid : (idx.getVar aig).validIn aig := by grind) : Aig :=
  let var := idx.getVar aig
  let aig := aig.setNode var <| .and lhs rhs
  let aig := aig.eraseLatch idx (by grind [setNode])
  aig

/--
  Convert a latch into a new and gate that defines the same variable, deleting the latch.

  If `idx` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `idx.getVar aig` is not valid in `aig`, throws `errVarInvalid`.
-/
@[always_inline]
def latchToAnd! (aig : Aig) (idx : LatchIdx) (lhs rhs : Lit) : Option Aig := do
  let h ← checkOrPanic (idx.validIn aig)              "Valaig.Aig.latchToAnd!" "`idx` not valid in `aig`"
  let h ← checkOrPanic ((idx.getVar aig).validIn aig) "Valaig.Aig.latchToAnd!" "`idx.getVar aig` not valid in `aig`"
  aig.latchToAnd idx lhs rhs

/--
  Change the latch index used to define a latch to a new known unused one.
  This is mainly useful when trying to build a new Aig while preserving indices from an existing one.
-/
@[inline]
def changeLatchIdx (aig : Aig) (old new : LatchIdx)
    (valid : old.validIn aig := by grind)
    (varValid : (old.getVar aig).validIn aig := by grind)
    (unused : ¬new.validIn aig ∨ old = new := by grind) : Aig :=
  let data := aig._latches[old.idx]
  let aig := aig.moveLatch old new
  let aig := aig.setNode data.val.var (.latch new data.val.var) (by grind [LatchIdx.getVar, Var.validIn, moveLatch, nodes])
  aig

/--
  Change the latch index used to define a latch to a new known unused one.
  This is mainly useful when trying to build a new Aig while preserving indices from an existing one.

  If `old` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `old.getVar aig` is not valid in `aig`, throws `errVarInvalid`.
  Otherwise if `new` is already valid in `aig` and not equal to `old`, throws `errUsed`.
-/
@[always_inline]
def changeLatchIdx! (aig : Aig) (old new : LatchIdx) : Option Aig := do
  let h ← checkOrPanic (old.validIn aig)              "Valaig.Aig.changeLatchIdx!" "`old` not valid in `aig`"
  let h ← checkOrPanic ((old.getVar aig).validIn aig) "Valaig.Aig.changeLatchIdx!" "`old.getVar aig` not valid in `aig`"
  let h ← checkOrPanic (¬new.validIn aig ∨ old = new) "Valaig.Aig.changeLatchIdx!" "`new` already used in `aig`"
  aig.changeLatchIdx old new

/--
  Convert an and gate to a new input.
-/
@[inline]
def andToInput (aig : Aig) (var : Var)
    (valid : var.validIn aig := by grind)
    (isAnd : aig[var] matches .and _ _ := by grind) : Aig × InputIdx :=
  let idx := aig.newInputIdx
  let aig := aig.setNode var <| .input idx var
  let aig := aig.pushInput { var } (by simp only [instGetElemVar, instGetElemVar.impl] at isAnd; grind)
  (aig, idx)

/--
  Convert an and gate to a new input.

  If `var` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `var` does not define an and gate, throws `errIsAnd`.
-/
@[always_inline]
def andToInput! (aig : Aig) (var : Var) : Option (Aig × InputIdx) := do
  let h ← checkOrPanic (var.validIn aig)           "Valaig.Aig.andToInput!" "`var` not valid in `aig`"
  let h ← checkOrPanic (aig[var] matches .and _ _) "Valaig.Aig.andToInput!" "`var` is not an and gate"
  aig.andToInput var

/--
  Convert an and gate to a new latch.
-/
def andToLatch (aig : Aig) (var : Var) (next : Lit) (reset : Option Lit := none)
    (valid : var.validIn aig := by grind)
    (isAnd : aig[var] matches .and _ _ := by grind) : Aig × LatchIdx :=
  let idx := aig.newLatchIdx
  let aig := aig.setNode var <| .latch idx var
  let aig := aig.pushLatch { var, next, reset } (by simp only [instGetElemVar, instGetElemVar.impl] at isAnd; grind)
  (aig, idx)

/--
  Convert an and gate to a new latch.

  If `var` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `var` does not define an and gate, throws `errIsAnd`.
-/
@[always_inline]
def andToLatch! (aig : Aig) (var : Var) (next : Lit) (reset : Option Lit := none) : Option (Aig × LatchIdx) := do
  let h ← checkOrPanic (var.validIn aig)           "Valaig.Aig.andToLatch!" "`var` not valid in `aig`"
  let h ← checkOrPanic (aig[var] matches .and _ _) "Valaig.Aig.andToLatch!" "`var` is not an and gate"
  aig.andToLatch var next reset

set_option linter.unusedVariables false in
/--
  Update the arguments to an existing and gate.
-/
@[inline]
def rewriteAnd (aig : Aig) (var : Var) (lhs rhs : Lit)
    (valid : var.validIn aig := by grind)
    (isAnd : aig[var] matches .and _ _ := by grind) : Aig :=
  aig.setNode var (.and lhs rhs)

/--
  Update the arguments to an existing and gate.

  If `var` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `var` does not define an and gate, throws `errIsAnd`.
-/
@[always_inline]
def rewriteAnd! (aig : Aig) (var : Var) (lhs rhs : Lit) : Option Aig := do
  let h ← checkOrPanic (var.validIn aig)           "Valaig.Aig.rewriteAnd!" "`var` not valid in `aig`"
  let h ← checkOrPanic (aig[var] matches .and _ _) "Valaig.Aig.rewriteAnd!" "`var` is not an and gate"
  aig.rewriteAnd var lhs rhs

-- TODO: Add convertToInput/convertToLatch/convertToAnd methods that do the right thing regardless
-- of a variable's current type, deallocing if needed

/--
A custom iterator type for the forward iteration of variables that is easy to reason about.
-/
@[ext]
structure VarIter (aig : Aig) where
  var : Var
  -- We store the end variable in the iterator to prevent holding a reference to the Aig
  endVar : Var
  sized : endVar = aig.nextVar := by grind
  range : var ≤ endVar := by grind

namespace VarIter

variable {m : Type -> Type _} [Pure m] {n : Type _ -> Type _}

attribute [local grind ext] Std.IterM VarIter

@[always_inline, local grind]
def step (it : @Std.IterM aig.VarIter m Var) : Std.IterStep (@Std.IterM aig.VarIter m Var) Var :=
  let var := it.internalState.var
  if h : it.internalState.var < it.internalState.endVar then
    .yield ⟨{ it.internalState with var := var + 1, range := by grind }⟩ var
  else
    .done

@[always_inline]
instance instIterator : Std.Iterator aig.VarIter m Var where
  IsPlausibleStep it step :=
    let var := it.internalState.var
    match step with
    | .done => var = it.internalState.endVar
    | .yield it' out => it'.internalState.var = var + 1 ∧ out = var
    | .skip _ => False

  step it := pure <| .deflate <| ⟨step it, by grind⟩

@[simp, local grind =]
theorem IsPlausibleStep_iff {it : @Std.IterM aig.VarIter m Var} {step} :
    it.IsPlausibleStep step ↔ VarIter.step it = step := by
  simp only [Std.IterM.IsPlausibleStep, Std.Iterator.IsPlausibleStep, instIterator, VarIter.step]
  grind

@[simp, local grind =]
theorem IsPlausibleSuccessorOf_iff {it it' : @Std.IterM aig.VarIter m Var} :
    it'.IsPlausibleSuccessorOf it ↔ (step it).successor = some it' := by
  grind [Std.IterM.IsPlausibleSuccessorOf]

open Std.Iterators in
private def instFinitenessRelation : FinitenessRelation aig.VarIter m where
  Rel := InvImage WellFoundedRelation.rel (aig.size - ·.internalState.var.idx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation h := by simp_wf; grind [nextVar]

instance instFinite : Std.Iterators.Finite aig.VarIter m := by
  exact .of_finitenessRelation instFinitenessRelation

@[always_inline]
instance instIteratorLoop [Monad m] [Monad n] : Std.IteratorLoop aig.VarIter m n :=
  .defaultImplementation

end VarIter

abbrev Iter (aig : Aig) := @Std.Iter aig.VarIter Var

/--
  A forward iterator over variables in the Aig.
  See also `iterVal`.
-/
@[inline]
def iter (aig : Aig) : aig.Iter :=
  ⟨VarIter.mk .constant aig.nextVar⟩

/--
  The next value to be returned by a variable iterator, or `iterEnd` if the
  iterator is done.
-/
@[inline]
def iterVal (aig : Aig) (it : aig.Iter) : Var :=
  it.internalState.var

/--
  The final variable iterator value that returns done.
-/
@[inline]
def iterEnd (aig : Aig) : aig.Iter :=
  ⟨VarIter.mk aig.nextVar aig.nextVar⟩

/--
  An iterator over inputs in the Aig.
-/
@[inline]
def inputsIter (aig : Aig) :=
  aig._inputs.iter.map InputIdx.ofIdx

/--
  An iterator over latches in the Aig.
-/
@[inline]
def latchesIter (aig : Aig) :=
  aig._latches.iter.map LatchIdx.ofIdx

/--
  An iterator over leaves in the Aig.
-/
@[inline]
def leaves (aig : Aig) :=
  aig.inputsIter.map LeafIdx.input |>.append <| aig.latchesIter.map LeafIdx.latch

end Valaig.Aig
