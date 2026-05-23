module

public meta import Valaig.Prelude
public import Valaig.Utils.Pool
public import Valaig.Utils.Map
public import Valaig.Aig.Refs
public import Valaig.ForStd

public section
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
-/
private abbrev InputData := { input : Input // input.var ≠ .constant }

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
-/
private abbrev LatchData := { latch : Latch // latch.var ≠ .constant }

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
-/
private abbrev NodeData := Lit × Lit

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
private def and (rhs0 rhs1 : Lit) : NodeData :=
  (rhs0, rhs1)

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
private theorem toNode_and {rhs0 rhs1 : Lit} {var : Var} (notConst : var ≠ .constant)
    (h0 : rhs0.var ≠ var) (h1 : rhs1.var ≠ var) :
    (and rhs0 rhs1).toNode var = .and rhs0 rhs1 := by
  grind

end NodeData

/--
  An output of interest in the circuit - this is also used to represent other
  referenced nodes in the Aiger format like bad and constraint nodes.
-/
structure Output where
  lit : Lit

namespace Output
deriving instance Hashable, DecidableEq, Repr, Inhabited for Output
end Output

abbrev Outputs := Array Output

end Aig

/--
  A sequential And-Inverter Graph consisting of inputs, latches and And gates.
-/
structure Aig where
  /-- The core array of nodes making up the Aig. -/
  private _nodes : Array Aig.NodeData

  /-- A mapping from input indices (`InputIdx`) to their definition. -/
  private _inputs : Utils.Pool Aig.InputData

  /-- A mapping from latch indices (`LatchIdx`) to their definition. -/
  private _latches : Utils.Pool Aig.LatchData

  /--
    We always store at least one element, which regardless of value represents the constant false.
  -/
  private sized : _nodes.size > 0

variable {aig : Aig}

namespace Aig

/--
  A general error type for fallible Aig functions.
-/
inductive Err
/-- Returned by `function!` functions if argument `arg` is invalid in the Aig when it is expected to be valid. -/
| invalidIdx (function : String) (arg : String)
/-- Generic error messages with an associated function. `Err.str` can be used to avoid defining a function location. -/
| other (function : String) (msg : String)

namespace Err
deriving instance Hashable, DecidableEq, Repr, Inhabited for Err

@[always_inline]
def str (msg : String) : Err :=
  .other "" msg

end Err

abbrev Except (α : Type) := _root_.Except Err α

@[always_inline]
instance : Utils.Map.AsNat Var where
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
def nodes (aig : Aig) : Utils.Map Var Node :=
  .mk
    (valid := (·.idx < aig._nodes.size))
    (map := fun var valid => aig._nodes[var.idx].toNode var)
    (size := aig._nodes.size)

@[always_inline]
instance : Utils.Map.AsNat InputIdx where
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
def inputs (aig : Aig) : Utils.Map InputIdx Input :=
  Utils.Map.ofPool aig._inputs InputIdx |>.mapVal (·.val)

@[always_inline]
instance : Utils.Map.AsNat LatchIdx where
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
def latches (aig : Aig) : Utils.Map LatchIdx Latch :=
  Utils.Map.ofPool aig._latches LatchIdx |>.mapVal (·.val)

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
  grind [nextVar, size, aig.sized]

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

/--
  An Aig with just the constant node.
-/
def empty : Aig :=
  {
    _nodes := #[.false],
    _inputs := .empty,
    _latches := .empty,
    sized := by grind
  }

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
  var.idx < aig.size

@[always_inline]
instance {var : Var} {aig : Aig} : Decidable (var.validIn aig) :=
  have : var.validIn aig ↔ var.idx < aig.size := by
    simp [Var.validIn]
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
@[local simp]
def validIn (idx : InputIdx) (aig : Aig) : Prop :=
  idx.idx ∈ aig._inputs

/-- NOTE: Do not rely on this function externally! -/
@[always_inline]
def instDecidableValidIn.impl (idx : InputIdx) (aig : Aig) : Bool :=
  idx.idx ∈ aig._inputs

@[always_inline]
instance {idx : InputIdx} : Decidable (idx.validIn aig) :=
  have : idx.validIn aig ↔ instDecidableValidIn.impl idx aig := by
    simp [instDecidableValidIn.impl]
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
@[local simp]
def validIn (idx : LatchIdx) (aig : Aig) : Prop :=
  idx.idx ∈ aig._latches

/-- NOTE: Do not rely on this function externally! -/
@[always_inline]
def instDecidableValidIn.impl (idx : LatchIdx) (aig : Aig) : Bool :=
  idx.idx ∈ aig._latches

@[always_inline]
instance {idx : LatchIdx} : Decidable (idx.validIn aig) :=
  have : idx.validIn aig ↔ instDecidableValidIn.impl idx aig := by
    simp [instDecidableValidIn.impl]
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

/-- NOTE: Do not rely on this function externally! -/
@[always_inline]
def instGetElemVar.impl (aig : Aig) (var : Var) (valid : var.validIn aig := by grind) : Node :=
  aig._nodes[var.idx].toNode var

@[always_inline]
instance instGetElemVar : GetElem Aig Var Node (fun aig var => var.validIn aig) where
  getElem aig var (h := by grind) :=
    instGetElemVar.impl aig var h

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

  If `idx` isn't valid in the Aig, throws `err`.
-/
@[always_inline]
def getVar! (idx : InputIdx) (aig : Aig) (err : Err := .invalidIdx "InputIdx.getVar!" "idx") : Except Var :=
  match aig._inputs[idx.idx]? with
  | some input => return input.val.var
  | none       => throw err

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
def getLit! (idx : InputIdx) (aig : Aig) (err : Err := .invalidIdx "InputIdx.getLit!" "idx") : Except Lit :=
  match aig._inputs[idx.idx]? with
  | some input => return input.val.var.toLit
  | none       => throw err

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
def getVar! (idx : LatchIdx) (aig : Aig) (err : Err := .invalidIdx "LatchIdx.getVar!" "idx") : Except Var :=
  match aig._latches[idx.idx]? with
  | some latch => return latch.val.var
  | none       => throw err

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
def getLit! (idx : LatchIdx) (aig : Aig) (err : Err := .invalidIdx "LatchIdx.getLit!" "idx") : Except Lit :=
  match aig._latches[idx.idx]? with
  | some latch => return latch.val.var.toLit
  | none       => throw err

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
def getNext! (idx : LatchIdx) (aig : Aig) (err : Err := .invalidIdx "LatchIdx.getNext!" "idx") : Except Lit :=
  match aig._latches[idx.idx]? with
  | some latch => return latch.val.next
  | none       => throw err

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
def getReset! (idx : LatchIdx) (aig : Aig) (err : Err := .invalidIdx "LatchIdx.getReset!" "idx") : Except (Option Lit) :=
  match aig._latches[idx.idx]? with
  | some latch => return latch.val.reset
  | none       => throw err

set_option linter.unusedVariables false in
/--
  Update the next state function for a latch in the Aig.
-/
@[inline]
def setNext (idx : LatchIdx) (aig : Aig) (next : Lit) (valid : idx.validIn aig := by grind) : Aig :=
  { aig with _latches := aig._latches.modify idx.idx (⟨{ ·.val with next }, by grind⟩) }

/--
  Update the next state function for a latch in the Aig.

  If `idx` isn't valid in the Aig, throws `err`.
-/
@[always_inline]
def setNext! (idx : LatchIdx) (aig : Aig) (next : Lit) (err : Err := .invalidIdx "LatchIdx.setNext!" "idx") : Except Aig :=
  if _ : idx.validIn aig then
    return idx.setNext aig next
  else
    throw err

set_option linter.unusedVariables false in
/--
  Update the reset function for a latch in the Aig.
-/
@[inline]
def setReset (idx : LatchIdx) (aig : Aig) (reset : Option Lit) (valid : idx.validIn aig := by grind) : Aig :=
  { aig with _latches := aig._latches.modify idx.idx (⟨{ ·.val with reset }, by grind⟩) }

/--
  Update the reset function for a latch in the Aig.

  If `idx` isn't valid in the Aig, throws `err`.
-/
@[always_inline]
def setReset! (idx : LatchIdx) (aig : Aig) (reset : Option Lit) (err : Err := .invalidIdx "LatchIdx.setReset!" "idx") : Except Aig :=
  if _ : idx.validIn aig then
    return idx.setReset aig reset
  else
    throw err

end LatchIdx

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
def getVar! (idx : LeafIdx) (aig : Aig) (err : Err := .invalidIdx "LeafIdx.getVar!" "idx") : Except Var :=
  match idx with
  | .input idx
  | .latch idx => idx.getVar! aig err

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
def getLit! (idx : LeafIdx) (aig : Aig) (err : Err := .invalidIdx "LeafIdx.getLit!" "idx") : Except Lit :=
  match idx with
  | .input idx
  | .latch idx => idx.getLit! aig err

end LeafIdx

/--
  Push a new node onto the `Aig` from its data. This has the variable `aig.nextVar`.
-/
@[always_inline]
private def pushNode (aig : Aig) (node : NodeData) : Aig :=
  { aig with _nodes := aig._nodes.push node, sized := by grind }

/--
  Overwrite a node at a given index in the `Aig`.
  TODO: This currently breaks linearity, so the existing node data is dealloced and
  a new node alloced.
-/
@[always_inline]
private def setNode (aig : Aig) (var : Var) (node : NodeData) (valid : var.validIn aig := by grind) : Aig :=
  { aig with _nodes := aig._nodes.set var.idx node, sized := by grind [aig.sized] }

@[always_inline]
private def insertInput (aig : Aig) (idx : InputIdx) (input : Input) (h : input.var ≠ .constant := by grind) : Aig :=
  { aig with _inputs := aig._inputs.insert idx.idx ⟨input, h⟩ }

@[always_inline]
private def insertLatch (aig : Aig) (idx : LatchIdx) (latch : Latch) (h : latch.var ≠ .constant := by grind) : Aig :=
  { aig with _latches := aig._latches.insert idx.idx ⟨latch, h⟩ }

@[always_inline]
private def eraseInput (aig : Aig) (idx : InputIdx) : Aig :=
  { aig with _inputs := aig._inputs.erase idx.idx }

@[always_inline]
private def eraseLatch (aig : Aig) (idx : LatchIdx) : Aig :=
  { aig with _latches := aig._latches.erase idx.idx }

attribute [local grind] InputIdx.validIn LatchIdx.validIn newInputIdx newLatchIdx

set_option linter.unusedVariables false in
/--
  Append an input with a new index to the Aig, returning the index of the input.
-/
@[always_inline]
def addInput (aig : Aig) : Aig × InputIdx :=
  let idx := aig.newInputIdx
  let var := aig.nextVar
  let aig := aig.pushNode <| .input idx var
  let aig := aig.insertInput idx { var }
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
  let aig := aig.insertLatch idx { var, next, reset }
  (aig, idx)

/--
  Append an and gate to the Aig, returning the variable defined by the new gate.
  This does not perform any optimizations.

  Note that neither input shuld be set to `nextVar` (equivalent to `Var.ofIdx aig.size`)
  or internal invariants are broken.
-/
@[always_inline]
def addAnd (aig : Aig) (rhs0 rhs1 : Lit) : Aig × Var :=
  let var := aig.nextVar
  let aig := aig.pushNode <| .and rhs0 rhs1
  (aig, var)

/--
  Convert an input into a new latch that defines the same variable, deleting the input.
-/
def InputIdx.convertToLatch (idx : InputIdx) (aig : Aig) (next : Lit) (reset : Option Lit := none)
    (valid : idx.validIn aig := by grind)
    (varValid : (idx.getVar aig).validIn aig := by grind) : Aig × LatchIdx :=
  let var := idx.getVar aig
  let latch := aig.newLatchIdx
  let aig := aig.setNode var <| .latch latch var
  let aig := aig.eraseInput idx
  let aig := aig.insertLatch latch { var, next, reset } (by grind [getVar])
  (aig, latch)

/--
  Convert an input into a new latch that defines the same variable, deleting the input.

  If `idx` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `idx.getVar aig` is not valid in `aig`, throws `errVarInvalid`.
-/
@[always_inline]
def InputIdx.convertToLatch! (idx : InputIdx) (aig : Aig) (next : Lit) (reset : Option Lit := none)
    (errInvalid    : Err := .invalidIdx "InputIdx.convertToLatch!" "idx")
    (errVarInvalid : Err := .invalidIdx "InputIdx.convertToLatch!" "idx.getVar aig") : Except (Aig × LatchIdx) :=
  if _ : ¬idx.validIn aig then
    throw errInvalid
  else if _ : ¬(idx.getVar aig).validIn aig then
    throw errVarInvalid
  else
    return idx.convertToLatch aig next reset

/--
  Convert an input into a new and gate that defines the same variable, deleting the input.
-/
@[inline]
def InputIdx.convertToAnd (idx : InputIdx) (aig : Aig) (rhs0 rhs1 : Lit)
    (valid : idx.validIn aig := by grind)
    (varValid : (idx.getVar aig).validIn aig := by grind) : Aig :=
  let var := idx.getVar aig
  let aig := aig.setNode var <| .and rhs0 rhs1
  let aig := aig.eraseInput idx
  aig

/--
  Convert an input into a new and gate that defines the same variable, deleting the input.

  If `idx` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `idx.getVar aig` is not valid in `aig`, throws `errVarInvalid`.
-/
@[always_inline]
def InputIdx.convertToAnd! (idx : InputIdx) (aig : Aig) (rhs0 rhs1 : Lit)
    (errInvalid    : Err := .invalidIdx "InputIdx.convertToAnd!" "idx")
    (errVarInvalid : Err := .invalidIdx "InputIdx.convertToAnd!" "idx.getVar aig") : Except Aig :=
  if _ : ¬idx.validIn aig then
    throw errInvalid
  else if _ : ¬(idx.getVar aig).validIn aig then
    throw errVarInvalid
  else
    return idx.convertToAnd aig rhs0 rhs1

set_option linter.unusedVariables false in
/--
  Change the input index used to define an input to a new known unused one.
  This is mainly useful when trying to build a new Aig while preserving indices from an existing one.
-/
@[inline]
def InputIdx.changeIdx (old new : InputIdx) (aig : Aig)
    (valid : old.validIn aig := by grind)
    (varValid : (old.getVar aig).validIn aig := by grind)
    (unused : ¬new.validIn aig ∨ old = new := by grind) : Aig :=
  let data := aig._inputs[old.idx]
  let var := data.val.var
  let aig := aig.setNode data.val.var (.input new data.val.var) (by grind [getVar])
  let aig := aig.eraseInput old
  let aig := aig.insertInput new data
  aig

/--
  Change the input index used to define an input to a new known unused one.
  This is mainly useful when trying to build a new Aig while preserving indices from an existing one.

  If `old` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `old.getVar aig` is not valid in `aig`, throws `errVarInvalid`.
  Otherwise if `new` is already valid in `aig` and not equal to `old`, throws `errUsed`.
-/
@[inline]
def InputIdx.changeIdx! (old new : InputIdx) (aig : Aig)
    (errInvalid    : Err := .invalidIdx "InputIdx.changeIdx!" "old")
    (errVarInvalid : Err := .invalidIdx "InputIdx.changeIdx!" "old.getVar aig")
    (errUsed       : Err := .other      "InputIdx.changeIdx!" "index new is already used") : Except Aig :=
  if _ : ¬old.validIn aig then
    throw errInvalid
  else if _ : ¬(old.getVar aig).validIn aig then
    throw errVarInvalid
  else if _ : new ≠ old ∧ new.validIn aig then
    throw errUsed
  else
    return old.changeIdx new aig

/--
  Convert a latch into a new input that defines the same variable, deleting the latch.
-/
def LatchIdx.convertToInput (idx : LatchIdx) (aig : Aig)
    (valid : idx.validIn aig := by grind)
    (varValid : (idx.getVar aig).validIn aig := by grind) : Aig × InputIdx :=
  let var := idx.getVar aig
  let input := aig.newInputIdx
  let aig := aig.setNode var <| .input input var
  let aig := aig.eraseLatch idx
  let aig := aig.insertInput input { var } (by grind [getVar])
  (aig, input)

/--
  Convert a latch into a new input that defines the same variable, deleting the latch.

  If `idx` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `idx.getVar aig` is not valid in `aig`, throws `errVarInvalid`.
-/
@[always_inline]
def LatchIdx.convertToInput! (idx : LatchIdx) (aig : Aig)
    (errInvalid    : Err := .invalidIdx "LatchIdx.convertToInput!" "idx")
    (errVarInvalid : Err := .invalidIdx "LatchIdx.convertToInput!" "idx.getVar aig") : Except (Aig × InputIdx) :=
  if _ : ¬idx.validIn aig then
    throw errInvalid
  else if _ : ¬(idx.getVar aig).validIn aig then
    throw errVarInvalid
  else
    return idx.convertToInput aig

/--
  Convert a latch into a new and gate that defines the same variable, deleting the latch.
-/
@[inline]
def LatchIdx.convertToAnd (idx : LatchIdx) (aig : Aig) (rhs0 rhs1 : Lit)
    (valid : idx.validIn aig := by grind)
    (varValid : (idx.getVar aig).validIn aig := by grind) : Aig :=
  let var := idx.getVar aig
  let aig := aig.setNode var <| .and rhs0 rhs1
  let aig := aig.eraseLatch idx
  aig

/--
  Convert a latch into a new and gate that defines the same variable, deleting the latch.

  If `idx` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `idx.getVar aig` is not valid in `aig`, throws `errVarInvalid`.
-/
@[always_inline]
def LatchIdx.convertToAnd! (idx : LatchIdx) (aig : Aig) (rhs0 rhs1 : Lit)
    (errInvalid    : Err := .invalidIdx "LatchIdx.convertToAnd!" "idx")
    (errVarInvalid : Err := .invalidIdx "LatchIdx.convertToAnd!" "idx.getVar aig") : Except Aig :=
  if _ : ¬idx.validIn aig then
    throw errInvalid
  else if _ : ¬(idx.getVar aig).validIn aig then
    throw errVarInvalid
  else
    return idx.convertToAnd aig rhs0 rhs1

set_option linter.unusedVariables false in
/--
  Change the latch index used to define a latch to a new known unused one.
  This is mainly useful when trying to build a new Aig while preserving indices from an existing one.
-/
@[inline]
def LatchIdx.changeIdx (old new : LatchIdx) (aig : Aig)
    (valid : old.validIn aig := by grind)
    (varValid : (old.getVar aig).validIn aig := by grind)
    (unused : ¬new.validIn aig ∨ old = new := by grind) : Aig :=
  let data := aig._latches[old.idx]
  let var := data.val.var
  let aig := aig.setNode data.val.var (.latch new data.val.var) (by grind [getVar])
  let aig := aig.eraseLatch old
  let aig := aig.insertLatch new data
  aig

/--
  Change the latch index used to define a latch to a new known unused one.
  This is mainly useful when trying to build a new Aig while preserving indices from an existing one.

  If `old` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `old.getVar aig` is not valid in `aig`, throws `errVarInvalid`.
  Otherwise if `new` is already valid in `aig` and not equal to `old`, throws `errUsed`.
-/
@[always_inline]
def LatchIdx.changeIdx! (old new : LatchIdx) (aig : Aig)
    (errInvalid    : Err := .invalidIdx "LatchIdx.changeIdx!" "old")
    (errVarInvalid : Err := .invalidIdx "LatchIdx.changeIdx!" "old.getVar aig")
    (errUsed       : Err := .other      "LatchIdx.changeIdx!" "index new is already used") : Except Aig :=
  if _ : ¬old.validIn aig then
    throw errInvalid
  else if _ : ¬(old.getVar aig).validIn aig then
    throw errVarInvalid
  else if _ : new ≠ old ∧ new.validIn aig then
    throw errUsed
  else
    return old.changeIdx new aig

set_option linter.unusedVariables false in
/--
  Convert an and gate to a new input.
-/
@[inline]
def convertAndToInput (aig : Aig) (var : Var)
    (valid : var.validIn aig := by grind)
    (isAnd : aig[var] matches .and _ _ := by grind) : Aig × InputIdx :=
  let idx := aig.newInputIdx
  let aig := aig.setNode var <| .input idx var
  let aig := aig.insertInput idx { var }
    (by simp only [instGetElemVar, instGetElemVar.impl, NodeData.toNode] at isAnd; grind)
  (aig, idx)

/--
  Convert an and gate to a new input.

  If `var` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `var` does not define an and gate, throws `errIsAnd`.
-/
@[always_inline]
def convertAndToInput! (aig : Aig) (var : Var)
    (errInvalid : Err := .invalidIdx "convertAndToInput!" "var")
    (errIsAnd   : Err := .other      "convertAndToInput!" "expected existing node to be an and gate") : Except (Aig × InputIdx) :=
  if _ : ¬var.validIn aig then
    throw errInvalid
  else if _ : ¬aig[var] matches .and _ _ then
    throw errIsAnd
  else
    return aig.convertAndToInput var

set_option linter.unusedVariables false in
/--
  Convert an and gate to a new latch.
-/
def convertAndToLatch (aig : Aig) (var : Var) (next : Lit) (reset : Option Lit := none)
    (valid : var.validIn aig := by grind)
    (isAnd : aig[var] matches .and _ _ := by grind) : Aig × LatchIdx :=
  let idx := aig.newLatchIdx
  let aig := aig.setNode var <| .latch idx var
  let aig := aig.insertLatch idx { var, next, reset }
    (by simp only [instGetElemVar, instGetElemVar.impl, NodeData.toNode] at isAnd; grind)
  (aig, idx)

/--
  Convert an and gate to a new latch.

  If `var` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `var` does not define an and gate, throws `errIsAnd`.
-/
@[always_inline]
def convertAndToLatch! (aig : Aig) (var : Var) (next : Lit) (reset : Option Lit := none)
    (errInvalid : Err := .invalidIdx "convertAndToLatch!" "var")
    (errIsAnd   : Err := .other      "convertAndToLatch!" "expected existing node to be an and gate") : Except (Aig × LatchIdx) :=
  if _ : ¬var.validIn aig then
    throw errInvalid
  else if _ : ¬aig[var] matches .and _ _ then
    throw errIsAnd
  else
    return aig.convertAndToLatch var next reset

set_option linter.unusedVariables false in
/--
  Update the arguments to an existing and gate.
-/
@[inline]
def rewriteAnd (aig : Aig) (var : Var) (rhs0 rhs1 : Lit)
    (valid : var.validIn aig := by grind)
    (isAnd : aig[var] matches .and _ _ := by grind) : Aig :=
  aig.setNode var (.and rhs0 rhs1)

/--
  Update the arguments to an existing and gate.

  If `var` is not valid in `aig`, throws `errInvalid`.
  Otherwise if `var` does not define an and gate, throws `errIsAnd`.
-/
@[always_inline]
def rewriteAnd! (aig : Aig) (var : Var) (rhs0 rhs1 : Lit)
    (errInvalid : Err := .invalidIdx "rewriteAnd!" "var")
    (errIsAnd   : Err := .other      "rewriteAnd!" "expected existing node to be an and gate") : Except Aig :=
  if _ : ¬var.validIn aig then
    throw errInvalid
  else if _ : ¬aig[var] matches .and _ _ then
    throw errIsAnd
  else
    return aig.rewriteAnd var rhs0 rhs1

-- TODO: Add convertToInput/convertToLatch/convertToAnd methods that do the right thing regardless
-- of a variable's current type, deallocing if needed

end Valaig.Aig
