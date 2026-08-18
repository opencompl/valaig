module

public import Valaig.Aig

public section
namespace Valaig.Transform
open Aig

namespace unroll

@[expose]
def assignMap (assign : LeafIdx -> Frame -> Bool) (map : Std.HashMap InputIdx InputIdx) : LeafIdx -> Frame -> Bool
| .input idx, frame =>
  match map.get? idx with
  | some idx => assign idx 1
  | none => assign idx frame
| idx, frame => assign idx frame

@[always_inline]
private def walker (old : WFAig) : old.CachingForwardsWalker (WFAig × Std.HashMap InputIdx InputIdx) Lit where
  stateMotive state size le := old ≤ state.fst ∧ ∀ idx, idx.validIn old → idx ∉ state.snd
  cacheMotive state size le sm var lt lit :=
    ∃ (h : lit.validIn state.fst),
      ∀ {assign},
        ⟦old, var, assign⟧cv1 = ⟦state.fst, lit, assignMap assign state.snd⟧c0

  init := ⟨old, .emptyWithCapacity old.numInputs⟩
  initState := by grind

  step var state cache valid size sm cm :=
    match _ : state.fst[var] with
    | .false       => (state, .false)
    | .and lhs rhs => let (eq:=_) (aig, var) := state.fst.addAnd (cache.mapLit lhs) (cache.mapLit rhs)
                      ((aig, state.snd), var)
    | .input idx   => let (eq:=h) (aig, idx') := state.fst.addInput;
                      ((aig, state.snd.insert idx' idx), idx'.getVar aig)
    | .latch idx   => (state, idx.getNext state.fst)

  stepState var state := by
    intros
    constructor
    · split <;> grind
    · grind [mem_inputs_newInputIdx (aig := state.fst)]
  stepCache var state cache valid _ _ sm cm var' hvar := by
    intros
    exists by intros; split <;> grind
    intro assign
    split
    · simp; grind
    · simp; grind
    next idx =>
      simp only [WFAig.raw_fst_addInput, WFAig.snd_addInput, snd_addInput]
      rw [denoteC_mono (mono_addInput (aig := state.fst))]
      · rcases cm hvar with ⟨_, cm⟩
        rw [cm]
        apply denoteC_of_assign_eq (wf := by grind)
        grind [assignMap]
      all_goals grind
    · simp; grind
  stepCacheNew var state cache valid _ sm cm := by
    intros
    exists by intros; split <;> grind
    intro assign
    split
    · simp; grind
    · simp; grind (splits := 100)
    · simp; grind [assignMap]
    next idx heq =>
      have : old.nodes[var] = Node.latch idx := by grind
      simp only [denoteCV_getElem_nodes_latch this, getNext_eq]
      have : state.fst.latches[idx] = old.latches[idx] := by grind
      rw [denoteC_mono sm.left (lit := state.fst.latches[idx].next)]
      · rw [Data.AbsMap.getElem_mono (mono_latches_mono sm.left)]
        · apply denoteC_of_assign_eq (wf := by grind)
          grind [assignMap]
        · grind
      all_goals grind

end unroll

/--
  Unroll the Aig by one time step. The second timestep is appended onto the existing circuit
  as a combinational function.

  TODO: Strashing whilst unrolling
-/
def unroll (aig : WFAig) : WFAig × Data.VarCache Lit × Std.HashMap InputIdx InputIdx :=
  let res := (unroll.walker aig).walk
  (res.fst.fst, res.snd, res.fst.snd)

@[simp, grind! .]
theorem mono_unroll (aig : WFAig) :
    aig ≤ (unroll aig).fst := by
  have := (unroll.walker aig).stateMotive_walk
  grind [unroll, unroll.walker]

@[simp, grind .]
theorem size_cache_unroll {aig : WFAig} :
    (unroll aig).snd.fst.size = aig.size := by
  have := (unroll.walker aig).stateMotive_walk
  grind [unroll, unroll.walker]

@[simp, grind .]
theorem mem_nodes_unroll_of_mem_cache {aig : WFAig} {var : Var} h :
    ((unroll aig).snd.fst[var]'h).var ∈ (unroll aig).fst.nodes := by
  have := (unroll.walker aig).cacheMotive_walk
  grind [unroll, unroll.walker]

@[simp, grind =]
theorem denote_unroll {assign} {aig : WFAig} {var : Var} mem :
    ⟦(unroll aig).fst, (unroll aig).snd.fst[var]'mem, unroll.assignMap assign (unroll aig).snd.snd⟧c0 =
      ⟦aig, var, assign⟧cv1 := by
  have := (unroll.walker aig).cacheMotive_walk var (by grind)
  grind [unroll, unroll.walker]

@[simp, grind .]
theorem unroll_not_mem_of_mem_inputs {aig : WFAig} {idx : InputIdx} (mem : idx ∈ aig.inputs) :
    idx ∉ (unroll aig).snd.snd := by
  have := (unroll.walker aig).stateMotive_walk
  grind [unroll, unroll.walker]

end Valaig.Transform
