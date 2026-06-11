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
  InputIdx.getVar InputIdx.getVar!
  InputIdx.getLit InputIdx.getLit!
  LatchIdx.getVar LatchIdx.getVar!
  LatchIdx.getLit LatchIdx.getLit!
  LatchIdx.getNext LatchIdx.getNext! setNext!
  LatchIdx.getReset LatchIdx.getReset! setReset!
  LeafIdx.validIn
  LeafIdx.getVar LeafIdx.getVar!
  LeafIdx.getLit LeafIdx.getLit!
  inputToLatch! inputToAnd! changeInputIdx!
  latchToInput! latchToAnd! changeLatchIdx!
  andToInput! andToLatch! rewriteAnd!

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

grind_pattern validIn_iff => var.idx, aig.size

@[simp, grind =]
theorem validIn_maxVar {var : Var} :
    var ≤ aig.maxVar ↔ var.validIn aig := by
  grind

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

@[simp, grind =]
theorem asAnd_eq {var : Var} (h : var.validIn aig) :
    aig.asAnd var h =
      match aig[var] with
      | .and lhs rhs => some (lhs, rhs)
      | _ => none := by
  rfl

@[simp, grind =]
theorem asAnd?_eq {var : Var} :
    aig.asAnd? var =
      match aig[var]? with
      | some (.and lhs rhs) => some (lhs, rhs)
      | _ => none := by
  rfl

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
  `setNext!`.
-/

@[simp, grind =]
theorem setNext!_eq {idx : LatchIdx} {next : Lit} valid :
    aig.setNext! idx next = aig.setNext idx next valid := by
  grind

@[grind →]
theorem setNext!_some {idx : LatchIdx} {next : Lit} {aig' : Aig} (ok : aig.setNext! idx next = aig') :
    aig' = aig.setNext idx next := by
  grind

/-
  `setReset!`
-/

@[simp, grind =]
theorem setReset!_eq {idx : LatchIdx} {reset : Option Lit} valid :
    aig.setReset! idx reset = aig.setReset idx reset valid := by
  grind

@[grind →]
theorem setReset!_some {idx : LatchIdx} {reset : Option Lit} {aig' : Aig} (ok : aig.setReset! idx reset = aig') :
    aig' = aig.setReset idx reset := by
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
  `inputToLatch!`.
-/

@[simp, grind =]
theorem inputToLatch!_eq {idx : InputIdx} {next : Lit} {reset : Option Lit} valid varValid :
    aig.inputToLatch! idx next reset = aig.inputToLatch idx next reset valid varValid := by
  simp; grind

@[grind →]
theorem inputToLatch!_some {idx : InputIdx} {next : Lit} {reset : Option Lit} {res : Aig × LatchIdx}
    (ok : aig.inputToLatch! idx next reset = res) :
    res = aig.inputToLatch idx next reset (varValid := by simp at ok; grind) := by
  grind

/-
  `inputToAnd!`.
-/

@[simp, grind =]
theorem inputToAnd!_eq {idx : InputIdx} {lhs rhs : Lit} valid varValid :
    aig.inputToAnd! idx lhs rhs = aig.inputToAnd idx lhs rhs valid varValid := by
  simp; grind

@[grind →]
theorem inputToAnd!_some {idx : InputIdx} {lhs rhs : Lit} {aig' : Aig}
    (ok : aig.inputToAnd! idx lhs rhs = aig') :
    aig' = aig.inputToAnd idx lhs rhs (varValid := by simp at ok; grind) := by
  grind

/-
  `changeInputIdx!`.
-/

@[simp, grind =]
theorem changeInputIdx!_eq {old new : InputIdx} valid varValid unused :
    aig.changeInputIdx! old new = aig.changeInputIdx old new valid varValid unused := by
  simp; grind

@[grind →]
theorem changeInputIdx!_some {old new : InputIdx} {aig' : Aig} (ok : aig.changeInputIdx! old new = aig') :
    aig' = aig.changeInputIdx old new
      (varValid := by simp at ok; grind)
      (unused := by simp at ok; grind) := by
  grind

/-
  `latchToInput!`.
-/

@[simp, grind =]
theorem latchToInput!_eq {idx : LatchIdx} valid varValid :
    aig.latchToInput! idx = aig.latchToInput idx valid varValid := by
  simp; grind

@[grind →]
theorem latchToInput!_some {idx : LatchIdx} {res : Aig × InputIdx} (ok : aig.latchToInput! idx = res) :
    res = aig.latchToInput idx (varValid := by simp at ok; grind) := by
  grind

/-
  `latchToAnd!`.
-/

@[simp, grind =]
theorem latchToAnd!_eq {idx : LatchIdx} {lhs rhs : Lit} valid varValid :
    aig.latchToAnd! idx lhs rhs = aig.latchToAnd idx lhs rhs valid varValid := by
  simp; grind

@[grind →]
theorem latchToAnd!_some {idx : LatchIdx} {lhs rhs : Lit} {aig' : Aig}
    (ok : aig.latchToAnd! idx lhs rhs = aig') :
    aig' = aig.latchToAnd idx lhs rhs (varValid := by simp at ok; grind) := by
  grind

/-
  `changeLatchIdx!`.
-/

@[simp, grind =]
theorem changeLatchIdx!_eq {old new : LatchIdx} valid varValid unused :
    aig.changeLatchIdx! old new = aig.changeLatchIdx old new valid varValid unused := by
  simp; grind

@[grind →]
theorem changeLatchIdx!_some {old new : LatchIdx} {aig' : Aig} (ok : aig.changeLatchIdx! old new = aig') :
    aig' = aig.changeLatchIdx old new
      (varValid := by simp at ok; grind)
      (unused := by simp at ok; grind) := by
  grind

/-
  `andToInput!`.
-/

@[simp, grind =]
theorem andToInput!_eq {var : Var} valid isAnd :
    aig.andToInput! var = aig.andToInput var valid isAnd := by
  simp; grind

@[grind →]
theorem andToInput!_some {var : Var} {res : Aig × InputIdx}
    (ok : aig.andToInput! var = res) :
    res = aig.andToInput var (isAnd := by simp at ok; grind) := by
  simp at ok; grind

/-
  `andToLatch!`.
-/

@[simp, grind =]
theorem andToLatch!_eq {var : Var} {next : Lit} {reset : Option Lit} valid isAnd :
    aig.andToLatch! var next reset = aig.andToLatch var next reset valid isAnd := by
  simp; grind

@[grind →]
theorem andToLatch!_some {var : Var} {next : Lit} {reset : Option Lit} {res : Aig × LatchIdx}
    (ok : aig.andToLatch! var next reset = res) :
    res = aig.andToLatch var next reset (isAnd := by simp at ok; grind) := by
  simp at ok; grind

/-
  `rewriteAnd!`.
-/

@[simp, grind =]
theorem rewriteAnd!_eq {var : Var} {lhs rhs : Lit} valid isAnd :
    aig.rewriteAnd! var lhs rhs = aig.rewriteAnd var lhs rhs valid isAnd := by
  simp; grind

@[grind →]
theorem rewriteAnd!_some {var : Var} {lhs rhs : Lit} {aig' : Aig}
    (ok : aig.rewriteAnd! var lhs rhs = aig') :
    aig' = aig.rewriteAnd var lhs rhs (isAnd := by simp at ok; grind) := by
  simp at ok; grind

end Valaig.Aig
