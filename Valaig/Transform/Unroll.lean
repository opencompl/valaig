module

public import Valaig.Aig
public import Valaig.Data.Memo

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

@[simp, grind unfold]
abbrev walker.info (aig : WFAig) : Data.Memo.VisitorInfo (Var.In aig) Lit (WFAig × Std.HashMap InputIdx InputIdx) where
  lt := (·.val < ·)
  stateInv state := aig ≤ state.fst ∧ ∀ idx, idx.validIn aig → idx ∉ state.snd
  cacheInv state sinv var lit :=
  ∃ (h : lit.validIn state.fst),
    ∀ {assign},
      ⟦aig, var, assign⟧cv1 = ⟦state.fst, lit, assignMap assign state.snd⟧c0

open Data.Memo.ActionM in
@[always_inline]
def walker (old : WFAig) : Data.Memo.Visitor (walker.info old) :=
  fun state var => do
    let map (lit : Lit) (valid : lit.var < var := by grind) :
        Data.Memo.ActionM _ _ _ { l : Lit // l.validIn state.fst } := do
      let new ← get ⟨lit.var, by grind⟩ valid
      return ⟨lit.mapTo new, by grind⟩

    match _ : state.fst[var.val] with
    | .false       => .just .false
    | .and lhs rhs => let (aig, var) := state.fst.addAnd (←map lhs) (←map rhs)
                      return ((aig, state.snd), var)
    | .input idx   => let res := state.fst.addInput
                      return ((res.fst, state.snd.insert res.snd idx), res.snd.getVar res.fst)
    | .latch idx   => .just (idx.getNext state.fst)

instance instWF {old : WFAig} : Data.Memo.WFVisitor (walker old) where
  stateInv state root hsi query _ walk hci := by
    intro res
    subst res
    apply walker.fun_cases_unfolding
      (motive := fun a => ∀ hpure, (walker.info old).stateInv ((a walk hci).value?.get hpure).fst)
    <;> simp only
    <;> intros
    <;> rename_i hpure
    <;> revert hpure
    <;> simp [-eq_self]
    <;> grind [mem_inputs_newInputIdx (aig := state.fst)]
  cacheInv state var hsi query _ walk hci := by
    apply walker.fun_cases_unfolding
      (motive := fun a => ∀ hpure hsi, (walker.info old).cacheInv ((a walk hci).value?.get hpure).fst hsi var ((a walk hci).value?.get hpure).snd)
    <;> simp only
    <;> intros
    <;> rename_i hpure hsi
    <;> revert hpure
    <;> simp [-eq_self]
    · grind
    · grind
    · grind [assignMap]
    · rename_i h
      intros
      exists by grind only [!WFAig.is_WF, WF.mem_nodes_next, usr WF.NextsValid_of_WF]
      simp only [WFAig.getElem_eq, getElem_eq] at h
      simp only [WFAig.le_iff] at hsi
      intro assign
      have := @denoteCV_getElem_nodes_latch (h := h) (frame := 1) (wf := by grind) (assign := assignMap assign state.snd)
      simp only [getNext_eq] at this
      simp only [←this, denoteCV_eq]
      rw [denoteC_mono hsi.left]
      · apply denoteC_of_assign_eq (wf := by grind)
        grind [assignMap]
      · grind
      · grind
      · grind
  cachePreservation state root var val hsi hci _ _ walk hci' := by
    apply walker.fun_cases_unfolding
      (motive := fun a => ∀ hpure hsi, (walker.info old).cacheInv ((a walk hci').value?.get hpure).fst hsi var val)
    <;> simp only
    <;> intros
    <;> rename_i hpure hsi
    <;> revert hpure
    <;> simp [-eq_self]
    · grind
    · grind
    · intros
      exists by grind
      intro assign
      rw [denoteC_mono (mono_addInput (aig := state.fst))]
      · simp only [exists_prop] at hci
        rw [hci.right]
        apply denoteC_of_assign_eq (wf := by grind)
        grind [assignMap]
      all_goals grind
    · grind
-- #exit

-- @[always_inline]
-- private def walker (old : WFAig) : old.CachingForwardsWalker (WFAig × Std.HashMap InputIdx InputIdx) Lit where
--   stateMotive state size le := old ≤ state.fst ∧ ∀ idx, idx.validIn old → idx ∉ state.snd
--   cacheMotive state size le sm var lt lit :=
--     ∃ (h : lit.validIn state.fst),
--       ∀ {assign},
--         ⟦old, var, assign⟧cv1 = ⟦state.fst, lit, assignMap assign state.snd⟧c0

--   init := ⟨old, .emptyWithCapacity old.numInputs⟩
--   initState := by grind

--   step var state cache valid size sm cm :=
--     match _ : state.fst[var] with
--     | .false       => (state, .false)
--     | .and lhs rhs => let (eq:=_) (aig, var) := state.fst.addAnd (cache.mapLit lhs) (cache.mapLit rhs)
--                       ((aig, state.snd), var)
--     | .input idx   => let (eq:=h) (aig, idx') := state.fst.addInput;
--                       ((aig, state.snd.insert idx' idx), idx'.getVar aig)
--     | .latch idx   => (state, idx.getNext state.fst)

--   stepState var state := by
--     intros
--     constructor
--     · split <;> grind
--     · grind [mem_inputs_newInputIdx (aig := state.fst)]
--   stepCache var state cache valid _ _ sm cm var' hvar := by
--     intros
--     exists by intros; split <;> grind
--     intro assign
--     split
--     · simp; grind
--     · simp; grind
--     next idx =>
--       simp only [WFAig.raw_fst_addInput, WFAig.snd_addInput, snd_addInput]
--       rw [denoteC_mono (mono_addInput (aig := state.fst))]
--       · rcases cm hvar with ⟨_, cm⟩
--         rw [cm]
--         apply denoteC_of_assign_eq (wf := by grind)
--         grind [assignMap]
--       all_goals grind
--     · simp; grind
--   stepCacheNew var state cache valid _ sm cm := by
--     intros
--     exists by intros; split <;> grind
--     intro assign
--     split
--     · simp; grind
--     · simp; grind (splits := 100)
--     · simp; grind [assignMap]
--     next idx heq =>
--       have : old.nodes[var] = Node.latch idx := by grind
--       simp only [denoteCV_getElem_nodes_latch this, getNext_eq]
--       have : state.fst.latches[idx] = old.latches[idx] := by grind
--       rw [denoteC_mono sm.left (lit := state.fst.latches[idx].next)]
--       · rw [Data.AbsMap.getElem_mono (mono_latches_mono sm.left)]
--         · apply denoteC_of_assign_eq (wf := by grind)
--           grind [assignMap]
--         · grind
--       all_goals grind

end unroll
/-

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
-/

end Valaig.Transform
