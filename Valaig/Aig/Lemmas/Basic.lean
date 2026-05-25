module

public import Valaig.Aig.Basic
import all Valaig.Aig.Basic
import Valaig.ForStd

public section

namespace Valaig.Aig
variable {aig : Aig}

attribute [local grind]
  nodes inputs latches
  size numInputs numLatches
  maxVar nextVar newInputIdx newLatchIdx
  numInputs numLatches numGates
  empty
  InputIdx.getVar InputIdx.getVar!
  InputIdx.getLit InputIdx.getLit!
  LatchIdx.getVar LatchIdx.getVar!
  LatchIdx.getLit LatchIdx.getLit!
  LatchIdx.getNext LatchIdx.getNext! LatchIdx.setNext!
  LatchIdx.getReset LatchIdx.getReset! LatchIdx.setReset!
  LeafIdx.validIn
  LeafIdx.getVar LeafIdx.getVar!
  LeafIdx.getLit LeafIdx.getLit!
  InputIdx.convertToLatch! InputIdx.convertToAnd! InputIdx.changeIdx!
  LatchIdx.convertToInput! LatchIdx.convertToAnd! LatchIdx.changeIdx!
  convertAndToInput! convertAndToLatch! rewriteAnd!

@[simp, grind =]
theorem toNat_Var {var : Var} :
    Utils.Map.AsNat.toNat var = var.idx := by
  rfl

@[simp, grind =]
theorem ofNat_Var {nat : Nat} :
    Utils.Map.AsNat.ofNat nat = Var.ofIdx nat := by
  rfl

@[simp, grind =]
theorem toNat_InputIdx {idx : InputIdx} :
    Utils.Map.AsNat.toNat idx = idx.idx := by
  rfl

@[simp, grind =]
theorem ofNat_InputIdx {nat : Nat} :
    Utils.Map.AsNat.ofNat nat = InputIdx.ofIdx nat := by
  rfl

@[simp, grind =]
theorem toNat_LatchIdx {idx : LatchIdx} :
    Utils.Map.AsNat.toNat idx = idx.idx := by
  rfl

@[simp, grind =]
theorem ofNat_LatchIdx {nat : Nat} :
    Utils.Map.AsNat.ofNat nat = LatchIdx.ofIdx nat := by
  rfl

@[simp, grind norm]
theorem size_eq :
    aig.size = aig.nodes.size := by
  grind

@[simp]
theorem size_ne_zero :
    aig.nodes.size > 0 :=
  aig.sized

grind_pattern size_ne_zero => aig.nodes.size

@[simp, grind norm]
theorem numInputs_eq :
    aig.numInputs = aig.inputs.size := by
  grind

@[simp, grind norm]
theorem numLatches_eq :
    aig.numLatches = aig.latches.size := by
  grind

@[simp, grind =]
theorem idx_maxVar :
    aig.maxVar.idx = aig.size - 1 := by
  grind

@[simp, grind =]
theorem validIn_maxVar {var : Var} :
    var ≤ aig.maxVar ↔ var.validIn aig := by
  grind [Var.validIn]

@[simp, grind =]
theorem idx_nextVar :
    aig.nextVar.idx = aig.size := by
  grind

@[simp, grind .]
theorem mem_nodes_nextVar :
    aig.nextVar ∉ aig.nodes := by
  grind

@[simp, grind =]
theorem le_nextVar {var : Var} :
    var ≤ aig.nextVar ↔ var ∈ aig.nodes ∨ var = aig.nextVar := by
  grind

@[simp, grind .]
theorem mem_inputs_newInputIdx :
    aig.newInputIdx ∉ aig.inputs := by
  grind

@[simp, grind .]
theorem mem_latches_newLatchIdx :
    aig.newLatchIdx ∉ aig.latches := by
  grind

@[simp, grind norm]
theorem var_validIn {var : Var} :
    var.validIn aig ↔ var ∈ aig.nodes := by
  grind [Var.validIn]

theorem mem_nodes_iff {var : Var} :
    var ∈ aig.nodes ↔ var < aig.nextVar := by
  grind [Var.validIn]

@[simp, grind norm]
theorem input_validIn {idx : InputIdx} :
    idx.validIn aig ↔ idx ∈ aig.inputs := by
  grind [InputIdx.validIn]

@[simp, grind norm]
theorem latch_validIn {idx : LatchIdx} :
    idx.validIn aig ↔ idx ∈ aig.latches := by
  grind [LatchIdx.validIn]

/-
  Some basic lemmas about index validity.
-/
section validIn

theorem validIn_mono {var var' : Var} (valid : var.validIn aig) (order : var' < var) :
    var'.validIn aig := by
  grind [Var.validIn]

grind_pattern validIn_mono => var.validIn aig, var'.validIn aig, var' < var

@[simp, grind .]
theorem mem_nodes_constant:
    Var.constant ∈ aig.nodes := by
  grind [aig.sized]

@[simp, grind .]
theorem false_validIn :
    Lit.false.validIn aig := by
  grind

@[simp, grind .]
theorem true_validIn :
    Lit.true.validIn aig := by
  grind

@[simp]
theorem validIn_size {var : Var} :
    var.idx < aig.nodes.size ↔ var.validIn aig := by
  grind [Var.validIn]

grind_pattern validIn_size => aig.nodes.size ≤ var.idx

@[simp, grind =]
theorem validIn_mapToVar {lit : Lit} {var : Var} :
    (lit.mapToVar var).validIn aig ↔ var.validIn aig := by
  grind

@[simp, grind =]
theorem validIn_mapTo {lit new : Lit} :
    (lit.mapTo new).validIn aig ↔ new.validIn aig := by
  grind

end validIn

@[simp, grind norm]
theorem getElem_eq {var : Var} valid :
    aig[var]'valid = aig.nodes[var] := by
  cbv

@[simp, grind =]
theorem getElem_nodes_constant :
    aig.nodes[Var.constant] = .false := by
  grind

@[simp, grind =]
theorem getElem_false_iff_constant {var : Var} valid :
    aig.nodes[var]'valid = .false ↔ var = .constant := by
  grind [NodeData.toNode]

@[simp, grind =]
theorem getElem?_eq {var : Var} :
    aig[var]? = if h : var.validIn aig then some aig[var] else none := by
  grind [getElem?_eq_some_getElem_iff]

@[simp]
theorem mem_nodes_of_getElem?_some {var : Var} {node : Node} (h : aig[var]? = some node) :
    var ∈ aig.nodes := by
  grind

grind_pattern mem_nodes_of_getElem?_some => aig[var]?, some node, var ∈ aig.nodes

-- TODO: Write some theorems about when ! variant functions return errors, and what errors
-- they return

/-
  `InputIdx.getVar`/`InputIdx.getVar!`.
-/

@[simp, grind norm]
theorem input_getVar_eq {idx : InputIdx} valid :
    idx.getVar aig valid = aig.inputs[idx].var := by
  grind

@[simp, grind =]
theorem input_getVar!_eq {idx : InputIdx} {err : Err} valid :
    idx.getVar! aig err = .ok (idx.getVar aig valid) := by
  grind

@[grind →]
theorem input_getVar!_ok {idx : InputIdx} {err : Err} {var : Var} (ok : idx.getVar! aig err = .ok var) :
    var = idx.getVar aig := by
  grind

/-
  `InputIdx.getLit`/`InputIdx.getLit!`.
-/

@[simp, grind norm]
theorem input_getLit_eq {idx : InputIdx} valid :
    idx.getLit aig valid = aig.inputs[idx].var.toLit := by
  grind

@[simp, grind =]
theorem input_getLit!_eq {idx : InputIdx} {err : Err} valid :
    idx.getLit! aig err = .ok (idx.getLit aig valid) := by
  grind

@[grind →]
theorem input_getLit!_ok {idx : InputIdx} {err : Err} {lit : Lit} (ok : idx.getLit! aig err = .ok lit) :
    lit = idx.getLit aig := by
  grind

/-
  `LatchIdx.getLit`/`LatchIdx.getLit!`.
-/

@[simp, grind norm]
theorem latch_getVar_eq {idx : LatchIdx} valid :
    idx.getVar aig valid = aig.latches[idx].var := by
  grind

@[simp, grind =]
theorem latch_getVar!_eq {idx : LatchIdx} {err : Err} valid :
    idx.getVar! aig err = .ok (idx.getVar aig valid) := by
  grind

@[grind →]
theorem latch_getVar!_ok {idx : LatchIdx} {err : Err} {var : Var} (ok : idx.getVar! aig err = .ok var) :
    var = idx.getVar aig := by
  grind

/-
  `LatchIdx.getVar`/`LatchIdx.getVar!`.
-/

@[simp, grind norm]
theorem latch_getLit_eq {idx : LatchIdx} valid :
    idx.getLit aig valid = aig.latches[idx].var.toLit := by
  grind

@[simp, grind =]
theorem latch_getLit!_eq {idx : LatchIdx} {err : Err} valid :
    idx.getLit! aig err = .ok (idx.getLit aig valid) := by
  grind

@[grind →]
theorem latch_getLit!_ok {idx : LatchIdx} {err : Err} {lit : Lit} (ok : idx.getLit! aig err = .ok lit) :
    lit = idx.getLit aig := by
  grind

/-
  `LatchIdx.getNext`/`LatchIdx.getNext!`.
-/

@[simp, grind norm]
theorem getNext_eq {idx : LatchIdx} valid :
    idx.getNext aig valid = aig.latches[idx].next := by
  grind

@[simp, grind =]
theorem getNext!_eq {idx : LatchIdx} {err : Err} valid :
    idx.getNext! aig err = .ok (idx.getNext aig valid) := by
  grind

@[grind →]
theorem getNext!_ok {idx : LatchIdx} {err : Err} {lit : Lit} (ok : idx.getNext! aig err = .ok lit) :
    lit = idx.getNext aig := by
  grind

/-
  `LatchIdx.getReset`/`LatchIdx.getReset!`.
-/

@[simp, grind norm]
theorem getReset_eq {idx : LatchIdx} valid :
    idx.getReset aig valid = aig.latches[idx].reset := by
  grind

@[simp, grind =]
theorem getReset!_eq {idx : LatchIdx} {err : Err} valid :
    idx.getReset! aig err = .ok (idx.getReset aig valid) := by
  grind

@[grind →]
theorem getReset!_ok {idx : LatchIdx} {err : Err} {lit : Lit} (ok : idx.getReset! aig err = .ok lit) :
    lit = idx.getReset aig := by
  grind

/-
  `LatchIdx.setNext!`.
-/

@[simp, grind =]
theorem setNext!_eq {idx : LatchIdx} {next : Lit} {err : Err} valid :
    idx.setNext! aig next err = .ok (idx.setNext aig next valid) := by
  grind

@[grind →]
theorem setNext!_ok {idx : LatchIdx} {next : Lit} {err : Err} {aig' : Aig} (ok : idx.setNext! aig next err = .ok aig') :
    aig' = idx.setNext aig next := by
  grind

/-
  `LatchIdx.setReset!`
-/

@[simp, grind =]
theorem setReset!_eq {idx : LatchIdx} {reset : Option Lit} {err : Err} valid :
    idx.setReset! aig reset err = .ok (idx.setReset aig reset valid) := by
  grind

@[grind →]
theorem setReset!_ok {idx : LatchIdx} {reset : Option Lit} {err : Err} {aig' : Aig} (ok : idx.setReset! aig reset err = .ok aig') :
    aig' = idx.setReset aig reset := by
  grind

namespace LeafIdx

@[simp, grind =]
theorem asInput_eq {idx : InputIdx} :
    (input idx).asInput = idx := by
  rfl

@[simp, grind =]
theorem asLatch_eq {idx : LatchIdx} :
    (latch idx).asLatch = idx := by
  rfl

@[simp, grind =]
theorem validIn_iff {idx : LeafIdx} :
    idx.validIn aig ↔
    match idx with
    | .input idx => idx.validIn aig
    | .latch idx => idx.validIn aig := by
  grind

/-
  `LeafIdx.getVar`/`LeafIdx.getVar!`.
-/

@[simp, grind =]
theorem getVar_eq {idx : LeafIdx} valid :
    idx.getVar aig valid =
    match idx with
    | .input idx
    | .latch idx => idx.getVar aig := by
  grind

@[simp, grind =]
theorem getVar!_eq {idx : LeafIdx} {err : Err} valid :
    idx.getVar! aig err = .ok (idx.getVar aig valid) := by
  grind

@[grind →]
theorem getVar!_ok {idx : LeafIdx} {err : Err} {var : Var} (ok : idx.getVar! aig err = .ok var) :
    var = idx.getVar aig := by
  grind

/-
  `LeafIdx.getLit`/`LeafIdx.getLit!`.
-/

@[simp, grind =]
theorem getLit_eq {idx : LeafIdx} valid :
    idx.getLit aig valid =
    match idx with
    | .input idx
    | .latch idx => idx.getLit aig := by
  grind

@[simp, grind =]
theorem getLit!_eq {idx : LeafIdx} {err : Err} valid :
    idx.getLit! aig err = .ok (idx.getLit aig valid) := by
  grind

@[grind →]
theorem getLit!_ok {idx : LeafIdx} {err : Err} {lit : Lit} (ok : idx.getLit! aig err = .ok lit) :
    lit = idx.getLit aig := by
  grind

end LeafIdx

/-
  `InputIdx.convertToLatch!`.
-/

@[simp, grind =]
theorem input_convertToLatch!_eq {idx : InputIdx} {next : Lit} {reset : Option Lit}
    {errInvalid errVarInvalid : Err} valid varValid :
    idx.convertToLatch! aig next reset errInvalid errVarInvalid =
    .ok (idx.convertToLatch aig next reset valid varValid) := by
  grind

@[grind →]
theorem input_convertToLatch!_ok {idx : InputIdx} {next : Lit} {reset : Option Lit}
    {errInvalid errVarInvalid : Err} {res : Aig × LatchIdx}
    (ok : idx.convertToLatch! aig next reset errInvalid errVarInvalid = .ok res) :
    res = idx.convertToLatch aig next reset := by
  grind

/-
  `InputIdx.convertToAnd!`.
-/

@[simp, grind =]
theorem input_convertToAnd!_eq {idx : InputIdx} {rhs0 rhs1 : Lit}
    {errInvalid errVarInvalid : Err} valid varValid :
    idx.convertToAnd! aig rhs0 rhs1 errInvalid errVarInvalid =
    .ok (idx.convertToAnd aig rhs0 rhs1 valid varValid) := by
  grind

@[grind →]
theorem input_convertToAnd!_ok {idx : InputIdx} {rhs0 rhs1 : Lit}
    {errInvalid errVarInvalid : Err} {aig' : Aig}
    (ok : idx.convertToAnd! aig rhs0 rhs1 errInvalid errVarInvalid = .ok aig') :
    aig' = idx.convertToAnd aig rhs0 rhs1 := by
  grind

/-
  `InputIdx.changeIdx!`.
-/

@[simp, grind =]
theorem input_changeIdx!_eq {old new : InputIdx} {errInvalid errVarInvalid errUsed : Err} valid varValid unused :
    old.changeIdx! new aig errInvalid errVarInvalid errUsed =
    .ok (old.changeIdx new aig valid varValid unused) := by
  grind

@[grind →]
theorem input_changeIdx!_ok {old new : InputIdx} {errInvalid errVarInvalid errUsed : Err} {aig' : Aig}
    (ok : old.changeIdx! new aig errInvalid errVarInvalid errUsed = .ok aig') :
    aig' = old.changeIdx new aig := by
  grind

/-
  `LatchIdx.convertToInput!`.
-/

@[simp, grind =]
theorem latch_convertToInput!_eq {idx : LatchIdx} {errInvalid errVarInvalid : Err} valid varValid :
    idx.convertToInput! aig errInvalid errVarInvalid =
    .ok (idx.convertToInput aig valid varValid) := by
  grind

@[grind →]
theorem latch_convertToInput!_ok {idx : LatchIdx} {errInvalid errVarInvalid : Err}
    {res : Aig × InputIdx} (ok : idx.convertToInput! aig errInvalid errVarInvalid = .ok res) :
    res = idx.convertToInput aig := by
  grind

/-
  `LatchIdx.convertToAnd!`.
-/

@[simp, grind =]
theorem latch_convertToAnd!_eq {idx : LatchIdx} {rhs0 rhs1 : Lit}
    {errInvalid errVarInvalid : Err} valid varValid :
    idx.convertToAnd! aig rhs0 rhs1 errInvalid errVarInvalid =
    .ok (idx.convertToAnd aig rhs0 rhs1 valid varValid) := by
  grind

@[grind →]
theorem latch_convertToAnd!_ok {idx : LatchIdx} {rhs0 rhs1 : Lit}
    {errInvalid errVarInvalid : Err} {aig' : Aig}
    (ok : idx.convertToAnd! aig rhs0 rhs1 errInvalid errVarInvalid = .ok aig') :
    aig' = idx.convertToAnd aig rhs0 rhs1 := by
  grind

/-
  `LatchIdx.changeIdx!`.
-/

@[simp, grind =]
theorem latch_changeIdx!_eq {old new : LatchIdx} {errInvalid errVarInvalid errUsed : Err} valid varValid unused :
    old.changeIdx! new aig errInvalid errVarInvalid errUsed = .ok (old.changeIdx new aig valid varValid unused) := by
  grind

@[grind →]
theorem latch_changeIdx!_ok {old new : LatchIdx} {errInvalid errVarInvalid errUsed : Err} {aig' : Aig}
    (ok : old.changeIdx! new aig errInvalid errVarInvalid errUsed = .ok aig') :
    aig' = old.changeIdx new aig := by
  grind

/-
  `convertAndToInput!`.
-/

@[simp, grind =]
theorem convertAndToInput!_eq {var : Var} {errInvalid errIsAnd : Err} valid isAnd :
    aig.convertAndToInput! var errInvalid errIsAnd =
    .ok (aig.convertAndToInput var valid isAnd) := by
  grind

@[simp, grind →]
theorem convertAndToInput!_ok {var : Var} {errInvalid errIsAnd : Err} {res : Aig × InputIdx}
    (ok : aig.convertAndToInput! var errInvalid errIsAnd = .ok res) :
    res = aig.convertAndToInput var := by
  grind

/-
  `convertAndToLatch!`.
-/

@[simp, grind =]
theorem convertAndToLatch!_eq {var : Var} {next : Lit} {reset : Option Lit}
    {errInvalid errIsAnd : Err} valid isAnd :
    aig.convertAndToLatch! var next reset errInvalid errIsAnd =
    .ok (aig.convertAndToLatch var next reset valid isAnd) := by
  grind

@[simp, grind →]
theorem convertAndToLatch!_ok {var : Var} {next : Lit} {reset : Option Lit}
    {errInvalid errIsAnd : Err} {res : Aig × LatchIdx}
    (ok : aig.convertAndToLatch! var next reset errInvalid errIsAnd = .ok res) :
    res = aig.convertAndToLatch var next reset := by
  grind

/-
  `rewriteAnd!`.
-/

@[simp, grind =]
theorem rewriteAnd!_eq {var : Var} {rhs0 rhs1 : Lit} {errInvalid errIsAnd : Err} valid isAnd :
    aig.rewriteAnd! var rhs0 rhs1 errInvalid errIsAnd =
    .ok (aig.rewriteAnd var rhs0 rhs1 valid isAnd) := by
  grind

@[simp, grind →]
theorem rewriteAnd!_ok {var : Var} {rhs0 rhs1 : Lit} {errInvalid errIsAnd : Err} {aig' : Aig}
    (ok : aig.rewriteAnd! var rhs0 rhs1 errInvalid errIsAnd = .ok aig') :
    aig' = aig.rewriteAnd var rhs0 rhs1 := by
  grind

end Valaig.Aig
