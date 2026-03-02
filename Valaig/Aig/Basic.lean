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
An index to an input definition in the Aig input array. These inputs are primary inputs (PIs).
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
A leaf in the combinational aig is either an input or a latch, which is just a reference back to
the index in the inputs or latches arrays.
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
  private aig : Std.Sat.AIG Aig.LeafIdx

  -- This is a temporary constraint, later we will enforce this by simply not storing a false node
  -- in the aig and always treating the constant variable as referring to false
  private hconst :
    ∀ (idx : Nat) (valid : idx < aig.decls.size),
      aig.decls[idx] = .false ↔ idx = 0

  -- A mapping from input indices (LeafIdx.input idx) to their definition
  private inputs : Aig.Inputs

  -- A mapping from latch indices (LeafIdx.latch idx) to their definition
  private latches : Aig.Latches

namespace Aig

variable {aig : Aig}

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
    hconst := by grind [Std.Sat.AIG.empty]
    inputs := #[],
    latches := #[],
  }

/--
The number of nodes currently allocated in aig.
-/
@[always_inline]
def size (aig : Aig) : Nat :=
  aig.aig.decls.size

/--
The maximum variable currently allocated in the aig.
-/
@[always_inline]
def maxVar (aig : Aig) : Var :=
  .ofIdx <| aig.size - 1

/--
The number of input nodes in the aig.
-/
@[always_inline]
def numInputs (aig : Aig) : Nat :=
  aig.inputs.size

/--
The number of latch nodes in the aig.
-/
@[always_inline]
def numLatches (aig : Aig) : Nat :=
  aig.latches.size

/--
The number of gate nodes in the aig.
-/
@[always_inline]
abbrev numGates (aig : Aig) : Nat :=
  aig.size - aig.numInputs - aig.numLatches - 1

end Aig

/-
Variable accessors.
-/
namespace Var 

def validIn (var : Var) (aig : Aig) : Prop :=
  var.idx < aig.size

@[always_inline]
instance {var : Var} {aig : Aig} : Decidable (var.validIn aig) :=
  have : var.validIn aig ↔ var.idx < aig.size := by
    simp [Var.validIn]
  decidable_of_iff' _ this

abbrev In (aig : Aig) := { var : Var // var.validIn aig }

@[always_inline, simp]
abbrev castIn (var : Var) (aig : Aig) (valid : var.validIn aig := by grind) : Var.In aig :=
  ⟨var, valid⟩

private theorem validIn_eq_lt_decls_size {var : Var} :
    var.validIn aig ↔ var.idx < aig.aig.decls.size := by
  grind [validIn, Aig.size]

grind_pattern validIn_eq_lt_decls_size => var.idx ≥ aig.aig.decls.size

@[simp]
private theorem validIn_of_lt_decls_size {var : Var} (valid : var.validIn aig) :
    var.idx < aig.aig.decls.size :=
  validIn_eq_lt_decls_size.mp valid

theorem validIn_eq_lt_size {var : Var} :
    var.validIn aig ↔ var.idx < aig.size := by
  grind [validIn]

grind_pattern validIn_eq_lt_size => var.idx ≥ aig.size

@[simp]
private theorem validIn_of_lt_size {var : Var} (valid : var.validIn aig) :
    var.idx < aig.size :=
  validIn_eq_lt_size.mp valid

end Var

namespace Lit

@[expose, reducible, simp, grind unfold]
def validIn (lit : Lit) (aig : Aig) : Prop :=
  lit.var.validIn aig

@[always_inline]
instance {lit : Lit} {aig : Aig} : Decidable (lit.validIn aig) :=
  have : lit.validIn aig ↔ lit.var.validIn aig := by simp
  decidable_of_iff' _ this

abbrev In (aig : Aig) := { lit : Lit // lit.validIn aig }

@[always_inline, simp]
abbrev castIn (lit : Lit ) (aig : Aig) (valid : lit.validIn aig := by grind) : Lit.In aig :=
  ⟨lit, valid⟩

end Lit

namespace Aig

variable {aig : Aig}

@[always_inline]
def get (aig : Aig) (var : Var) (valid : var.validIn aig := by grind) : Node :=
  match aig.aig.decls[var.idx] with
  | .false => .false
  | .atom (.input idx) => .input idx
  | .atom (.latch idx) => .latch idx
  | .gate rhs0 rhs1 => .and (.ofFanin rhs0) (.ofFanin rhs1)

@[local simp]
private theorem getElem_decls_eq_get {idx : Nat} (valid : idx < aig.aig.decls.size) :
    aig.aig.decls[idx] =
    match aig.get (Var.ofIdx idx) (by grind [Var.validIn, size]) with
    | .false     => .false
    | .input idx => .atom (.input idx)
    | .latch idx => .atom (.latch idx)
    | .and rhs0 rhs1 => .gate rhs0.toFanin rhs1.toFanin := by
  grind [Aig.get]

@[local simp]
private theorem get_eq_getElem_decls {var : Var} (valid : var.validIn aig) :
    aig.get var valid =
    match aig.aig.decls[var.idx]'valid with
    | .false     => .false
    | .atom (.input idx) => .input idx
    | .atom (.latch idx) => .latch idx
    | .gate rhs0 rhs1 => .and (.ofFanin rhs0) (.ofFanin rhs1) := by
  grind [Aig.get]

@[always_inline, expose, reducible, grind unfold]
instance instGetElemVar : GetElem Aig Var Node (fun aig var => var.validIn aig) where
  getElem aig var (h := by grind) :=
    aig.get var h

@[simp]
theorem getElem_eq_get {var : Var} (valid : var.validIn aig) :
    aig[var]'valid = aig.get var valid := by
  rfl

/-
Input accessors.
-/
namespace InputIdx

@[local simp]
def validIn (idx : InputIdx) (aig : Aig) : Prop :=
  idx.idx < aig.numInputs

@[always_inline]
instance {idx : InputIdx} {aig : Aig} : Decidable (idx.validIn aig) :=
  have : idx.validIn aig ↔ idx.idx < aig.numInputs := by
    simp [validIn]
  decidable_of_iff' _ this

abbrev In (aig : Aig) := { idx : InputIdx // idx.validIn aig }

@[always_inline, simp]
abbrev castIn (idx : InputIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : InputIdx.In aig :=
  ⟨idx, valid⟩

@[always_inline]
def getVar (idx : InputIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Var :=
  aig.inputs[idx.idx].var

@[always_inline, simp]
abbrev getLit (idx : InputIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Lit :=
  idx.getVar aig valid |>.toLit

end InputIdx

/-
Latch accessors.
-/
namespace LatchIdx

@[local simp]
def validIn (idx : LatchIdx) (aig : Aig) : Prop :=
  idx.idx < aig.numLatches

@[always_inline]
instance {idx : LatchIdx} {aig : Aig} : Decidable (idx.validIn aig) :=
  have : idx.validIn aig ↔ idx.idx < aig.numLatches := by
    simp [validIn]
  decidable_of_iff' _ this

abbrev In (aig : Aig) := { idx : LatchIdx // idx.validIn aig }

@[always_inline, simp]
abbrev castIn (idx : LatchIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : LatchIdx.In aig :=
  ⟨idx, valid⟩

@[always_inline]
def getVar (idx : LatchIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Var :=
  aig.latches[idx.idx].var

@[always_inline, simp]
abbrev getLit (idx : LatchIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Lit :=
  idx.getVar aig valid |>.toLit

@[always_inline]
def getNext (idx : LatchIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Lit :=
  aig.latches[idx.idx].next

@[always_inline]
def setNext (idx : LatchIdx) (aig : Aig) (next : Lit) (valid : idx.validIn aig := by grind) : Aig :=
  { aig with latches := aig.latches.modifyMem idx.idx (by simp_all [numLatches]) ({ ·.val with next }) }

@[always_inline]
def getReset (idx : LatchIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Lit :=
  aig.latches[idx.idx].reset

@[always_inline]
def setReset (idx : LatchIdx) (aig : Aig) (reset : Lit) (valid : idx.validIn aig := by grind) : Aig :=
  { aig with latches := aig.latches.modifyMem idx.idx (by simp_all [numLatches]) ({ ·.val with reset }) }

end LatchIdx

theorem numInputs_zero_iff_not_validIn :
    aig.numInputs = 0 ↔ ∀ (idx : InputIdx), ¬idx.validIn aig := by
  simp [InputIdx.validIn]
  constructor
  · grind
  · intro h
    have := h (.ofIdx 0)
    grind

theorem numLatches_zero_iff_not_validIn :
    aig.numLatches = 0 ↔ ∀ (idx : LatchIdx), ¬idx.validIn aig := by
  simp [LatchIdx.validIn]
  constructor
  · grind
  · intro h
    have := h (.ofIdx 0)
    grind

/-
Arbitrary index validity and accessors, defined as abbreviations
-/
namespace LeafIdx

@[inline]
def asInput (idx : LeafIdx) (h : idx matches .input _ := by grind) : InputIdx :=
  match idx, h with
  | .input idx, _ => idx

@[simp, grind =]
theorem asInput_of_input {idx : InputIdx} :
    (input idx).asInput = idx := by
  rfl

@[inline]
def asLatch (idx : LeafIdx) (h : idx matches .latch _ := by grind) : LatchIdx :=
  match idx, h with
  | .latch idx, _ => idx

@[simp, grind =]
theorem asLatch_of_latch {idx : LatchIdx} :
    (latch idx).asLatch = idx := by
  rfl

def validIn (idx : LeafIdx) (aig : Aig) : Prop :=
  match idx with
  | .input idx => idx.validIn aig
  | .latch idx => idx.validIn aig

@[simp]
theorem validIn_def {idx : LeafIdx} :
    idx.validIn aig ↔
    match idx with
    | .input idx => idx.validIn aig
    | .latch idx => idx.validIn aig := by
  grind [validIn]

-- Only unfold with this pattern when not trivially an input or latch
grind_pattern validIn_def => idx.validIn aig where
  idx =/= .input _
  idx =/= .latch _

@[simp, grind =]
theorem validIn_input {idx : InputIdx} :
    (input idx).validIn aig ↔ idx.validIn aig := by
  grind [validIn]

@[simp, grind =]
theorem validIn_latch {idx : LatchIdx} :
    (latch idx).validIn aig ↔ idx.validIn aig := by
  grind [validIn]

instance {idx : InputIdx} : Coe (idx.validIn aig) ((idx : LeafIdx).validIn aig) where
  coe := by grind

instance {idx : LatchIdx} : Coe (idx.validIn aig) ((idx : LeafIdx).validIn aig) where
  coe := by grind

@[always_inline]
instance {idx : LeafIdx} {aig : Aig} : Decidable (idx.validIn aig) := by
  rw [validIn_def]
  match idx with
  | .input idx => infer_instance
  | .latch idx => infer_instance

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

@[always_inline]
def getVar (idx : LeafIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Var :=
  match idx with
  | .input idx => idx.getVar aig
  | .latch idx => idx.getVar aig

@[simp]
theorem getVar_def {idx : LeafIdx} (valid : idx.validIn aig) :
    idx.getVar aig valid =
    match idx with
    | .input idx => idx.getVar aig
    | .latch idx => idx.getVar aig := by
  grind [getVar]

grind_pattern getVar_def => idx.getVar aig where
  idx =/= .input _
  idx =/= .latch _

@[simp, grind =]
theorem getVar_input {idx : InputIdx} (valid : (input idx).validIn aig) :
    (input idx).getVar aig = idx.getVar aig := by
  grind [getVar]

@[simp, grind =]
theorem getVar_latch {idx : LatchIdx} (valid : (latch idx).validIn aig) :
    (latch idx).getVar aig = idx.getVar aig := by
  grind [getVar]

@[always_inline, expose, simp, grind unfold]
def getLit (idx : LeafIdx) (aig : Aig) (valid : idx.validIn aig := by grind) : Lit :=
  idx.getVar aig valid |>.toLit

end LeafIdx

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
  have hconst := by grind [aig.aig.hzero, aig.hconst, Std.mkAtom_eq_decls_push]
  let aig := { aig with aig := res.aig, hconst, inputs }
  (aig, idx)

@[inline]
def addLatch (aig : Aig) (next reset : Lit) : Aig × LatchIdx :=
  let idx := .ofIdx aig.latches.size
  let res := aig.aig.mkAtom <| .latch idx
  let latch := { var := .ofRef res.ref, next, reset }
  let latches := aig.latches.push latch
  have hconst := by grind [aig.aig.hzero, aig.hconst, Std.mkAtom_eq_decls_push]
  let aig := { aig with aig := res.aig, hconst,  latches }
  (aig, idx)

-- TODO: Currently this requires proofs that rhs0/rhs1 are valid in the aig, but after switching to
-- buffed (and getting rid of dependent typing) this won't be needed anymore
@[inline]
def addAnd (aig : Aig) (rhs0 rhs1 : Lit)
    (valid0 : rhs0.validIn aig := by grind) (valid1 : rhs1.validIn aig := by grind) : Aig × Lit :=
  let res := aig.aig.mkAndCached ⟨rhs0.toRef valid0, rhs1.toRef valid1⟩
  have hconst := by
    intro i
    by_cases i ≥ aig.aig.decls.size
    <;> grind [aig.aig.hzero, aig.hconst, aig.aig.mkAndCached_decl_eq, Std.mkAndCached_matches_gate (aig := aig.aig)]
  let aig := { aig with aig := res.aig, hconst }
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
attribute [simp_valaig_defs] Var.ext_idx

attribute [simp_valaig_defs, grind_valaig_defs =]
  Std.mkAtom_eq_decls_push Std.mkAtom_size Std.mkAtom_ref_eq_decls_size
  Std.Sat.AIG.mkAndCached_decl_eq

attribute [grind_valaig_defs! .] Std.Sat.AIG.mkAndCached_le_size
