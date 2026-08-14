module

public import Valaig.Aig

public section
namespace Valaig.Transform
open Aig

namespace unroll

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
        ⟦old, var, 1, assign⟧sv = ⟦state.fst, lit, 0, assignMap assign state.snd⟧s

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
      rw [denoteS_mono (mono_addInput (aig := state.fst))]
      · rcases cm hvar with ⟨_, cm⟩
        rw [cm]
        apply denoteS_of_assign_eq (wf := by grind)
        grind [assignMap]
      all_goals grind
    · simp; grind
  stepCacheNew var state cache valid _ sm cm := by
    intros
    exists by intros; split <;> grind
    intro assign
    split
    · simp; grind
    · simp; grind
    · simp; grind [assignMap]
    next idx heq =>
      have : old.nodes[var] = Node.latch idx := by grind
      simp only [denoteSV_getElem_nodes_latch this, getNext_eq]
      have : state.fst.latches[idx] = old.latches[idx] := by grind
      rw [denoteS_mono sm.left (lit := state.fst.latches[idx].next)]
      · rw [Data.AbsMap.getElem_mono (mono_latches_mono sm.left)]
        · apply denoteS_of_assign_eq (wf := by grind)
          grind [assignMap]
        · grind
      all_goals grind

end unroll

/--
  Unroll the Aig by one time step. The second timestep is appended onto the existing circuit
  as a combinational function.

  TODO: Strashing whilst unrolling
-/
def unroll (aig : WFAig) : WFAig × Data.VarCache Lit :=
  let res := (unroll.walker aig).walk
  (res.fst.fst, res.snd)

end Valaig.Transform
