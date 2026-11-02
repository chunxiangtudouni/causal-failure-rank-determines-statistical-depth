module

public import Structure.PA06_A19Prepare_StaticMetadata036_StageIteration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Complete equality-row scan and actual conditional stage store. Empty
supports need no special oracle: they simply match no nonempty tree node. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass loadRel storeRel setRel incrementRel)

theorem stageTail_effect (rom : PhysicalROM) (CB count counter exit : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hc : state.heap (CB + counter) = count) :
    let after := runOps rom (incrementRel counter ++ jumpTo exit) state
    after.register .address = CB ∧ after.heap = Function.update state.heap (CB + counter) (count + 1) ∧
      after.pc = 5 * exit ∧ after.halted = state.halted := by
  simp [incrementRel, loadRel, storeRel, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute, hCB, hc]

def stageNodeFinishHeap (q : Nat) (full : List (Finset (Fin q))) (reference : NatState)
    (CB P stage node : Nat) (heap : Nat → Nat) : Nat → Nat :=
  let stored := if stageMatchTools (rawIncidenceROM q full) reference.heap CB (mass q full) stage node q then
    Function.update heap (fieldAddress P full.length (preparedSize q full) .stage stage) (node + 1) else heap
  Function.update stored (CB + 19) (node + 1)

private theorem stageNodeFinishHeap_apply (q : Nat) (full : List (Finset (Fin q)))
    (reference : NatState) (CB P stage node : Nat) (heap : Nat → Nat) (address : Nat) :
    stageNodeFinishHeap q full reference CB P stage node heap address =
      if address = CB + 19 then node + 1 else
      if stageMatchTools (rawIncidenceROM q full) reference.heap CB (mass q full) stage node q then
        if address = fieldAddress P full.length (preparedSize q full) .stage stage then node + 1 else heap address
      else heap address := by
  simp only [stageNodeFinishHeap, Function.update_apply, ite_apply]

theorem stage_node_finish_ready (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (reference : NatState)
    (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId) (pointer nextPointer : Nat)
    (before after : NatState) (ready : StageToolReady q full CB P reference stage node q pointer before)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hh : after.heap = stageNodeFinishHeap q full reference CB P stage.val node.val before.heap)
    (hCB : after.register .address = CB) (hpc : after.pc = nextPointer) (ha : after.halted = false) :
    StageNodeReady q full CB P reference stage (node.val + 1) nextPointer after ∧ StageFrame q full CB P before after := by
  have below := stage_region_below_control q full CB P hlayout
  have hs := stage.isLt
  have hstage : fieldAddress P full.length (preparedSize q full) .stage stage.val < CB := by
    simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
    omega
  have outside_control (address offset : Nat) (ha : address < CB) : address ≠ CB + offset := by
    omega
  have frame : StageFrame q full CB P before after := by
    intro address hn
    have h19 : address ≠ CB + 19 := by unfold StageAllowed at hn; omega
    have hst : address ≠ fieldAddress P full.length (preparedSize q full) .stage stage.val := by
      unfold StageAllowed fieldAddress fieldFactor fieldExtra at *
      omega
    rw [hh]
    simp [stageNodeFinishHeap_apply, h19, hst]
  refine ⟨?_, frame⟩
  constructor
  · exact ScanInput.of_stageFrame ready.input hlayout frame hCB
  · rw [hh]
    simp (disch := omega) [stageNodeFinishHeap_apply, (outside_control _ 22 hstage).symm, ready.stage_cell]
  · rw [hh]
    simp only [stageNodeFinishHeap, Function.update_self]
  · rw [hh]
    simp (disch := omega) [stageNodeFinishHeap_apply, outside_control _ 19 hstage, scanWinner, ready.current_stage]
  · intro earlier he
    have he' := earlier.isLt
    have ha' : fieldAddress P full.length (preparedSize q full) .stage earlier.val < CB := by
      simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
      omega
    have hne : fieldAddress P full.length (preparedSize q full) .stage earlier.val ≠
        fieldAddress P full.length (preparedSize q full) .stage stage.val := by
      simp only [fieldAddress]
      omega
    rw [hh]
    simpa (disch := omega) [stageNodeFinishHeap_apply, outside_control _ 19 ha', hne] using ready.stages earlier he
  · exact hpc
  · exact ha

section Actual
variable (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
  (reference : NatState) (referenceData : RawCardData q full CB reference)
  (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
  (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)

include referenceData hlayout code

theorem stage_tool_scan_partial (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId)
    (before : NatState) (ready : StageToolReady q full CB P reference stage node 0 (5 * (start + 51)) before)
    (count : Nat) (hc : count ≤ q) :
    ∃ clock ≤ 90 * count,
      let after := natRun (rawIncidenceROM q full) containing clock before
      StageToolReady q full CB P reference stage node count (5 * (start + 51)) after ∧ StageFrame q full CB P before after := by
  revert hc
  induction count with
  | zero =>
    intro _
    exact ⟨0, by omega, ready, StageFrame.refl q full CB P before⟩
  | succ count ih =>
    intro hc
    obtain ⟨previousClock, hp, previousReady, previousFrame⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing previousClock before
    obtain ⟨nextClock, hn, nextReady, nextFrame⟩ := stage_tool_iteration q full CB P reference referenceData
      hlayout containing start code stage node ⟨count, by omega⟩ previous previousReady
    refine ⟨previousClock + nextClock, by omega, ?_⟩
    rw [natRun_add]
    exact ⟨nextReady, previousFrame.trans nextFrame⟩

omit referenceData in
theorem stage_node_initialize (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId)
    (before : NatState) (ready : StageNodeReady q full CB P reference stage node.val (5 * (start + 34)) before) :
    let after := natRun (rawIncidenceROM q full) containing 17 before
    StageToolReady q full CB P reference stage node 0 (5 * (start + 51)) after ∧ StageFrame q full CB P before after := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (scanBoundedTest 2 19 (start + 191)) before
  have hp : tested.pc = 5 * (start + 43) := by
    rw [scanBoundedTest_pc rom CB (preparedSize q full) node.val 2 19 (start + 191) before
      ready.input.address ready.input.nodes ready.node_cell, ite_eq_right (by have hn : node.val < preparedSize q full := node.isLt; omega), ready.pc]
    omega
  have ha : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  have testedHeap : tested.heap = before.heap := rfl
  have testedCB : tested.register .address = CB := ready.input.address
  let after := runOps rom stageNodeInitialize tested
  have hh : after.heap = Function.update (Function.update before.heap (CB + 23) 1) (CB + 20) 0 := by
    simp [after, stageNodeInitialize, setRel, storeRel, runOps, natExecuteOp, Op.execute, Instruction.execute, testedCB, testedHeap]
  have frame : StageFrame q full CB P before after := by
    intro address hn
    have h20 : address ≠ CB + 20 := by unfold StageAllowed at hn; omega
    have h23 : address ≠ CB + 23 := by unfold StageAllowed at hn; omega
    rw [hh]
    simp [h20, h23]
  have hCB : after.register .address = CB := ready.input.address
  have below := stage_region_below_control q full CB P hlayout
  have hs := stage.isLt
  have hstage : fieldAddress P full.length (preparedSize q full) .stage stage.val < CB := by
    simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
    omega
  have hpc : after.pc = 5 * (start + 51) := by
    rw [runOps_pc rom _ tested (by simp [stageNodeInitialize, setRel, storeRel, NoJump]), hp,
      show stageNodeInitialize.length = 8 from rfl]
    omega
  have next : StageToolReady q full CB P reference stage node 0 (5 * (start + 51)) after := by
    constructor
    · exact ScanInput.of_stageFrame ready.input hlayout frame hCB
    · rw [hh]; simp [ready.stage_cell]
    · rw [hh]; simp [ready.node_cell]
    · rw [hh, Function.update_self]
    · rw [hh]; simp [stageMatchTools, bit]
    · rw [hh]; simpa (disch := omega) [Function.update_apply] using ready.current_stage
    · intro earlier he
      have he' := earlier.isLt
      have ha' : fieldAddress P full.length (preparedSize q full) .stage earlier.val < CB := by
        simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
        omega
      rw [hh]; simpa (disch := omega) [Function.update_apply] using ready.stages earlier he
    · exact hpc
    · exact (runOps_halted rom _ tested).trans ha
  have testedRun : natRun (rawIncidenceROM q full) containing 9 before = tested :=
    stage_chunk_run rom containing start code .nodeTest before ready.pc ready.active
  have initializedRun : natRun (rawIncidenceROM q full) containing 8 tested = after :=
    stage_chunk_run rom containing start code .nodeInitialize tested hp ha
  rw [show (17 : Nat) = 9 + 8 by decide, natRun_add, testedRun, initializedRun]
  exact ⟨next, frame⟩

omit referenceData in
theorem stage_node_finish (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId)
    (before : NatState) (ready : StageToolReady q full CB P reference stage node q (5 * (start + 51)) before) :
    ∃ clock ≤ 46,
      let after := natRun (rawIncidenceROM q full) containing clock before
      StageNodeReady q full CB P reference stage (node.val + 1) (5 * (start + 34)) after ∧ StageFrame q full CB P before after := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (scanBoundedTest 1 20 (start + 154)) before
  have htPC : tested.pc = 5 * (start + 154) := by
    rw [scanBoundedTest_pc rom CB q q 1 20 (start + 154) before
      ready.input.address ready.input.tools ready.tool_cell, Nat.sub_self, ite_eq_left rfl]
  have htActive : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  let checked := runOps rom (stageNodeWriteTest (start + 180)) tested
  let matched := stageMatchTools rom reference.heap CB (mass q full) stage.val node.val q
  have hcPC : checked.pc = if matched then 5 * (start + 159) else 5 * (start + 180) := by
    rw [stageNodeWriteTest_pc rom CB _ (start + 180) tested ready.input.address ready.match_cell, htPC]
    change (if bit matched = 0 then _ else _) = _
    cases matched <;> simp [bit]; omega
  have hcActive : checked.halted = false := (runOps_halted rom _ tested).trans htActive
  let stored := if matched then runOps rom stageRecord checked else checked
  have below := stage_region_below_control q full CB P hlayout
  have hs := stage.isLt
  have hstage : fieldAddress P full.length (preparedSize q full) .stage stage.val < CB := by
    simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
    omega
  have storedHeap : stored.heap = if matched then
      Function.update before.heap (fieldAddress P full.length (preparedSize q full) .stage stage.val) (node.val + 1) else before.heap := by
    by_cases hm : matched = true
    · simp only [stored, hm, ite_true]
      exact (stageRecord_effect rom CB P full.length (preparedSize q full) stage.val node.val checked
        ready.input.address ready.input.base ready.input.nodes ready.stage_cell ready.node_cell).2
    · simp only [stored, hm]
      rfl
  have storedCB : stored.register .address = CB := by
    by_cases hm : matched = true <;> simp only [stored, hm, ite_true] <;> exact ready.input.address
  have storedPC : stored.pc = 5 * (start + 180) := by
    by_cases hm : matched = true
    · simp only [stored, hm, ite_true]
      have matchedPC : checked.pc = 5 * (start + 159) := by
        simpa only [hm, ite_true] using hcPC
      rw [runOps_pc rom _ checked (by simp [stageRecord, loadRel, storeField, fieldPointer, fieldPointerLead, fieldPointerExtra, NoJump]),
        matchedPC, show stageRecord.length = 21 from rfl]
      omega
    · simpa [stored, hm] using hcPC
  have storedActive : stored.halted = false := by
    by_cases hm : matched = true
    · simpa only [stored, hm, ite_true] using (runOps_halted rom stageRecord checked).trans hcActive
    · simpa [stored, hm] using hcActive
  have storedNode : stored.heap (CB + 19) = node.val := by
    rw [storedHeap]
    split_ifs <;> simp (disch := omega) [ready.node_cell]
  let after := runOps rom (stageNodeTail start) stored
  have tail : after.register .address = CB ∧
      after.heap = Function.update stored.heap (CB + 19) (node.val + 1) ∧
      after.pc = 5 * (start + 34) ∧ after.halted = stored.halted := by
    simpa only [after, stageNodeTail] using
      (stageTail_effect rom CB node.val 19 (start + 34) stored storedCB storedNode)
  have hh : after.heap = stageNodeFinishHeap q full reference CB P stage.val node.val before.heap := by
    rw [tail.2.1, storedHeap]
    rfl
  have next := stage_node_finish_ready q full CB P reference stage node (5 * (start + 51)) (5 * (start + 34))
    before after ready hlayout hh tail.1 tail.2.2.1 ((tail.2.2.2).trans storedActive)
  have headRun : natRun rom containing (9 + 5) before = checked := by
    have testedRun : natRun rom containing 9 before = tested :=
      stage_chunk_run rom containing start code .toolTest before ready.pc ready.active
    have checkedRun : natRun rom containing 5 tested = checked :=
      stage_chunk_run rom containing start code .writeTest tested htPC htActive
    rw [natRun_add, testedRun, checkedRun]
  have storeRun : natRun rom containing (if matched then 21 else 0) checked = stored := by
    by_cases hm : matched = true
    · simp only [stored, hm, ite_true]
      exact stage_chunk_run rom containing start code .record checked
        (by simpa only [hm, ite_true, stageChunkOffset] using hcPC) hcActive
    · simp [stored, hm]
      rfl
  have tailRun : natRun rom containing 11 stored = after :=
    stage_chunk_run rom containing start code .nodeTail stored storedPC storedActive
  refine ⟨(9 + 5) + (if matched then 21 else 0) + 11, by split_ifs <;> omega, ?_⟩
  rw [natRun_add, natRun_add, headRun, storeRun, tailRun]
  exact next

theorem stage_node_iteration (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId)
    (before : NatState) (ready : StageNodeReady q full CB P reference stage node.val (5 * (start + 34)) before) :
    ∃ clock ≤ 63 + 90 * q,
      let after := natRun (rawIncidenceROM q full) containing clock before
      StageNodeReady q full CB P reference stage (node.val + 1) (5 * (start + 34)) after ∧ StageFrame q full CB P before after := by
  let initialized := natRun (rawIncidenceROM q full) containing 17 before
  obtain ⟨initReady, initFrame⟩ := stage_node_initialize q full CB P reference hlayout containing start code stage node before ready
  obtain ⟨scanClock, hscan, scanReady, scanFrame⟩ := stage_tool_scan_partial q full CB P reference referenceData
    hlayout containing start code stage node initialized initReady q le_rfl
  let scanned := natRun (rawIncidenceROM q full) containing scanClock initialized
  obtain ⟨finishClock, hfinish, next, finishFrame⟩ := stage_node_finish q full CB P reference hlayout containing start code stage node scanned scanReady
  refine ⟨17 + scanClock + finishClock, by omega, ?_⟩
  rw [natRun_add, natRun_add]
  exact ⟨next, (initFrame.trans scanFrame).trans finishFrame⟩

end Actual
end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
