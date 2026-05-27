module

public import Valaig.Aig.Basic
import all Valaig.Aig.Basic
import Valaig.ForLean.Iter

public section

open Valaig.Data (AbsMap)

namespace Valaig.Aig
variable {aig : Aig}

attribute [local grind] nodes inputs latches
attribute [local simp, local grind]
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
    AbsMap.AsNat.toNat var = var.idx := by
  rfl

@[simp, grind =]
theorem ofNat_Var {nat : Nat} :
    AbsMap.AsNat.ofNat nat = Var.ofIdx nat := by
  rfl

@[simp, grind =]
theorem toNat_InputIdx {idx : InputIdx} :
    AbsMap.AsNat.toNat idx = idx.idx := by
  rfl

@[simp, grind =]
theorem ofNat_InputIdx {nat : Nat} :
    AbsMap.AsNat.ofNat nat = InputIdx.ofIdx nat := by
  rfl

@[simp, grind =]
theorem toNat_LatchIdx {idx : LatchIdx} :
    AbsMap.AsNat.toNat idx = idx.idx := by
  rfl

@[simp, grind =]
theorem ofNat_LatchIdx {nat : Nat} :
    AbsMap.AsNat.ofNat nat = LatchIdx.ofIdx nat := by
  rfl

@[simp, grind norm]
theorem size_eq :
    aig.size = aig.nodes.size := by
  grind

@[simp]
theorem size_ne_zero :
    aig.nodes.size > 0 := by
  simp [nodes]

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

theorem validIn_iff {var : Var} :
    var.validIn aig ↔ var.idx < aig.size := by
  rfl

@[simp, grind =]
theorem validIn_maxVar {var : Var} :
    var ≤ aig.maxVar ↔ var.validIn aig := by
  grind [validIn_iff]

@[simp, grind =]
theorem idx_nextVar :
    aig.nextVar.idx = aig.size := by
  grind

@[simp, grind .]
theorem mem_nodes_nextVar :
    aig.nextVar ∉ aig.nodes := by
  grind [validIn_iff]

@[simp, grind =]
theorem le_nextVar {var : Var} :
    var ≤ aig.nextVar ↔ var ∈ aig.nodes ∨ var = aig.nextVar := by
  grind [validIn_iff]

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
  grind [validIn_iff]

attribute [local grind =] validIn_iff

theorem mem_nodes_iff {var : Var} :
    var ∈ aig.nodes ↔ var < aig.nextVar := by
  grind

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
  grind

grind_pattern validIn_mono => var.validIn aig, var'.validIn aig, var' < var

@[simp, grind .]
theorem mem_nodes_constant:
    Var.constant ∈ aig.nodes := by
  grind

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
  grind

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
theorem input_getVar!_eq {idx : InputIdx} valid :
    idx.getVar! aig = idx.getVar aig valid := by
  grind

@[grind →]
theorem input_getVar!_some {idx : InputIdx} {var : Var} (ok : idx.getVar! aig = var) :
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
theorem input_getLit!_eq {idx : InputIdx}  valid :
    idx.getLit! aig = idx.getLit aig valid := by
  grind

@[grind →]
theorem input_getLit!_some {idx : InputIdx} {lit : Lit} (ok : idx.getLit! aig = lit) :
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
theorem latch_getVar!_eq {idx : LatchIdx} valid :
    idx.getVar! aig = idx.getVar aig valid := by
  grind

@[grind →]
theorem latch_getVar!_some {idx : LatchIdx} {var : Var} (ok : idx.getVar! aig = var) :
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
theorem latch_getLit!_eq {idx : LatchIdx} valid :
    idx.getLit! aig = idx.getLit aig valid := by
  grind

@[grind →]
theorem latch_getLit!_some {idx : LatchIdx} {lit : Lit} (ok : idx.getLit! aig = lit) :
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
theorem getNext!_eq {idx : LatchIdx} valid :
    idx.getNext! aig = idx.getNext aig valid := by
  grind

@[grind →]
theorem getNext!_some {idx : LatchIdx} {lit : Lit} (ok : idx.getNext! aig = lit) :
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
theorem getReset!_eq {idx : LatchIdx} valid :
    idx.getReset! aig = some (idx.getReset aig valid) := by
  grind

@[grind →]
theorem getReset!_some {idx : LatchIdx} {lit : Lit} (ok : idx.getReset! aig = lit) :
    lit = idx.getReset aig := by
  grind

/-
  `LatchIdx.setNext!`.
-/

@[simp, grind =]
theorem setNext!_eq {idx : LatchIdx} {next : Lit} valid :
    idx.setNext! aig next = idx.setNext aig next valid := by
  grind

@[grind →]
theorem setNext!_some {idx : LatchIdx} {next : Lit} {aig' : Aig} (ok : idx.setNext! aig next = aig') :
    aig' = idx.setNext aig next := by
  grind

/-
  `LatchIdx.setReset!`
-/

@[simp, grind =]
theorem setReset!_eq {idx : LatchIdx} {reset : Option Lit} valid :
    idx.setReset! aig reset = idx.setReset aig reset valid := by
  grind

@[grind →]
theorem setReset!_some {idx : LatchIdx} {reset : Option Lit} {aig' : Aig} (ok : idx.setReset! aig reset = aig') :
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
theorem getVar!_eq {idx : LeafIdx} valid :
    idx.getVar! aig = idx.getVar aig valid := by
  grind

@[grind →]
theorem getVar!_some {idx : LeafIdx} {var : Var} (ok : idx.getVar! aig = var) :
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
theorem getLit!_eq {idx : LeafIdx} valid :
    idx.getLit! aig = idx.getLit aig valid := by
  grind

@[grind →]
theorem getLit!_some {idx : LeafIdx} {lit : Lit} (ok : idx.getLit! aig = lit) :
    lit = idx.getLit aig := by
  grind

end LeafIdx

/-
  `InputIdx.convertToLatch!`.
-/

@[simp, grind =]
theorem input_convertToLatch!_eq {idx : InputIdx} {next : Lit} {reset : Option Lit} valid varValid :
    idx.convertToLatch! aig next reset = idx.convertToLatch aig next reset valid varValid := by
  simp; grind

@[grind →]
theorem input_convertToLatch!_some {idx : InputIdx} {next : Lit} {reset : Option Lit} {res : Aig × LatchIdx}
    (ok : idx.convertToLatch! aig next reset = res) :
    res = idx.convertToLatch aig next reset (varValid := by simp at ok; grind) := by
  grind

/-
  `InputIdx.convertToAnd!`.
-/

@[simp, grind =]
theorem input_convertToAnd!_eq {idx : InputIdx} {rhs0 rhs1 : Lit} valid varValid :
    idx.convertToAnd! aig rhs0 rhs1 = idx.convertToAnd aig rhs0 rhs1 valid varValid := by
  simp; grind

@[grind →]
theorem input_convertToAnd!_some {idx : InputIdx} {rhs0 rhs1 : Lit} {aig' : Aig}
    (ok : idx.convertToAnd! aig rhs0 rhs1 = aig') :
    aig' = idx.convertToAnd aig rhs0 rhs1 (varValid := by simp at ok; grind) := by
  grind

/-
  `InputIdx.changeIdx!`.
-/

@[simp, grind =]
theorem input_changeIdx!_eq {old new : InputIdx} valid varValid unused :
    old.changeIdx! new aig = old.changeIdx new aig valid varValid unused := by
  simp; grind

@[grind →]
theorem input_changeIdx!_some {old new : InputIdx} {aig' : Aig} (ok : old.changeIdx! new aig = aig') :
    aig' = old.changeIdx new aig
      (varValid := by simp at ok; grind)
      (unused := by simp at ok; grind) := by
  grind

/-
  `LatchIdx.convertToInput!`.
-/

@[simp, grind =]
theorem latch_convertToInput!_eq {idx : LatchIdx} valid varValid :
    idx.convertToInput! aig = idx.convertToInput aig valid varValid := by
  simp; grind

@[grind →]
theorem latch_convertToInput!_some {idx : LatchIdx} {res : Aig × InputIdx}
    (ok : idx.convertToInput! aig = res) :
    res = idx.convertToInput aig (varValid := by simp at ok; grind) := by
  grind

/-
  `LatchIdx.convertToAnd!`.
-/

@[simp, grind =]
theorem latch_convertToAnd!_eq {idx : LatchIdx} {rhs0 rhs1 : Lit} valid varValid :
    idx.convertToAnd! aig rhs0 rhs1 =
    idx.convertToAnd aig rhs0 rhs1 valid varValid := by
  simp; grind

@[grind →]
theorem latch_convertToAnd!_some {idx : LatchIdx} {rhs0 rhs1 : Lit} {aig' : Aig}
    (ok : idx.convertToAnd! aig rhs0 rhs1 = aig') :
    aig' = idx.convertToAnd aig rhs0 rhs1 (varValid := by simp at ok; grind) := by
  grind

/-
  `LatchIdx.changeIdx!`.
-/

@[simp, grind =]
theorem latch_changeIdx!_eq {old new : LatchIdx} valid varValid unused :
    old.changeIdx! new aig = old.changeIdx new aig valid varValid unused := by
  simp; grind

@[grind →]
theorem latch_changeIdx!_some {old new : LatchIdx} {aig' : Aig}
    (ok : old.changeIdx! new aig = aig') :
    aig' = old.changeIdx new aig
      (varValid := by simp at ok; grind)
      (unused := by simp at ok; grind) := by
  grind

/-
  `convertAndToInput!`.
-/

@[simp, grind =]
theorem convertAndToInput!_eq {var : Var} valid isAnd :
    aig.convertAndToInput! var = aig.convertAndToInput var valid isAnd := by
  simp; grind

@[grind →]
theorem convertAndToInput!_some {var : Var} {res : Aig × InputIdx}
    (ok : aig.convertAndToInput! var = res) :
    res = aig.convertAndToInput var (isAnd := by simp at ok; grind) := by
  simp at ok; grind

/-
  `convertAndToLatch!`.
-/

@[simp, grind =]
theorem convertAndToLatch!_eq {var : Var} {next : Lit} {reset : Option Lit} valid isAnd :
    aig.convertAndToLatch! var next reset = aig.convertAndToLatch var next reset valid isAnd := by
  simp; grind

@[grind →]
theorem convertAndToLatch!_some {var : Var} {next : Lit} {reset : Option Lit} {res : Aig × LatchIdx}
    (ok : aig.convertAndToLatch! var next reset = res) :
    res = aig.convertAndToLatch var next reset (isAnd := by simp at ok; grind) := by
  simp at ok; grind

/-
  `rewriteAnd!`.
-/

@[simp, grind =]
theorem rewriteAnd!_eq {var : Var} {rhs0 rhs1 : Lit} valid isAnd :
    aig.rewriteAnd! var rhs0 rhs1 = aig.rewriteAnd var rhs0 rhs1 valid isAnd := by
  simp; grind

@[grind →]
theorem rewriteAnd!_some {var : Var} {rhs0 rhs1 : Lit} {aig' : Aig}
    (ok : aig.rewriteAnd! var rhs0 rhs1 = aig') :
    aig' = aig.rewriteAnd var rhs0 rhs1 (isAnd := by simp at ok; grind) := by
  simp at ok; grind

end Valaig.Aig
