module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordStageNodeJointNumeric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNVALIDATED actual202 node iteration. The conditional record and its
real branch length are kept in one witness with semantics/frame/RunFacts.
No existential time from the Nat-only stage_node_finish is identified with
an independently selected safety time. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass loadRel storeRel setRel actualPackedWords actualControlBase actualAllocation RunFacts)

theorem stage_node_initialize_runFacts (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)
    (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (ready : StageNodeReady q full (actualControlBase q full) (actualPackedWords q full)
      reference stage node.val (5 * (start + 34)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
      (rawIncidenceROM q full) containing 17 before := by
  let rom := rawIncidenceROM q full
  let B := metadataWordLimit (indexWidth 32 full.length q)
  let H := actualAllocation q full
  let CB := actualControlBase q full
  let M := mass q full
  have room := PA06A19PrepareChildrenCache023.highCacheEnd_actual_fits q full hq
  have hH : H ≤ B := metadata_le_wordLimit room.2.1
  have htM : preparedSize q full ≤ M := prepared_indexed_size_le q full
  have hn : node.val < preparedSize q full := node.isLt
  have exitBound : 5 * (start + 191) ≤ B := by
    have hb := code.1
    have hc : 5 * containing.length ≤ B := metadata_le_wordLimit hcodePC
    omega
  let tested := runOps rom (scanBoundedTest 2 19 (start + 191)) before
  have testPC : tested.pc = 5 * (start + 43) := by
    rw [scanBoundedTest_pc rom CB (preparedSize q full) node.val 2 19 (start + 191) before
      ready.input.address ready.input.nodes ready.node_cell, ite_eq_right (by omega), ready.pc]
    omega
  have testActive : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  have testNumeric := scanBoundedTest_numeric rom B H CB M (preparedSize q full) node.val
    2 19 (start + 191) before (fun reg => metadata_le_wordLimit (hr reg))
    ready.input.address ready.input.nodes ready.node_cell (by decide) (by decide)
    htM (by omega) exitBound room.1 hH
  have testSafe := stage_chunk_safe_at rom B H containing start code .nodeTest before
    ready.pc ready.active testNumeric 43 (by decide) testPC
  change RunFacts B H rom containing 9 before at testSafe
  have testRun : natRun rom containing 9 before = tested :=
    stage_chunk_run rom containing start code .nodeTest before ready.pc ready.active
  have testRegs : RegistersLE B tested := by
    have h := ((testSafe.1).final _ _ _ _ _).1
    rw [testRun] at h
    exact h
  have initNumeric := stageNodeInitialize_numeric rom B H CB M tested testRegs ready.input.address room.1 hH
  have initPC : (runOps rom stageNodeInitialize tested).pc = 5 * (start + 51) := by
    rw [runOps_pc rom _ tested (by simp [stageNodeInitialize, setRel, storeRel, NoJump]), testPC, show stageNodeInitialize.length = 8 from rfl]
    omega
  have initSafe := stage_chunk_safe_at rom B H containing start code .nodeInitialize tested
    testPC testActive initNumeric 51 (by decide) initPC
  change RunFacts B H rom containing 8 tested at initSafe
  exact RunFacts.add B H rom containing 9 8 before testSafe (by rw [testRun]; exact initSafe)

def stageNodeFinishClock (q : Nat) (full : List (Finset (Fin q))) (reference : NatState)
    (CB stage node : Nat) : Nat :=
  (9 + 5) + (if stageMatchTools (rawIncidenceROM q full) reference.heap CB (mass q full) stage node q
    then 21 else 0) + 11

theorem stage_node_finish_joint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)
    (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (ready : StageToolReady q full (actualControlBase q full) (actualPackedWords q full)
      reference stage node q (5 * (start + 51)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    ∃ clock ≤ 46,
      clock = stageNodeFinishClock q full reference (actualControlBase q full) stage.val node.val ∧
      let after := natRun (rawIncidenceROM q full) containing clock before
      StageNodeReady q full (actualControlBase q full) (actualPackedWords q full)
        reference stage (node.val + 1) (5 * (start + 34)) after ∧
      StageFrame q full (actualControlBase q full) (actualPackedWords q full) before after ∧
      RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
        (rawIncidenceROM q full) containing clock before := by
  let rom := rawIncidenceROM q full
  let B := metadataWordLimit (indexWidth 32 full.length q)
  let H := actualAllocation q full
  let CB := actualControlBase q full
  let P := actualPackedWords q full
  let M := mass q full
  have layout : CB = 4 + P + 4096 * (mass q full + preparedSize q full) := rfl
  have room := PA06A19PrepareChildrenCache023.highCacheEnd_actual_fits q full hq
  have hH : H ≤ B := metadata_le_wordLimit room.2.1
  have qM : q ≤ M := by dsimp only [M, mass]; omega
  have htM : preparedSize q full ≤ M := prepared_indexed_size_le q full
  have hn : node.val < preparedSize q full := node.isLt
  have one : 1 ≤ B := by
    have h := room.1
    unfold PA06A19PrepareChildrenCache023.highCacheEnd at h
    omega
  have jump (offset : Nat) (ho : offset ≤ 202) : 5 * (start + offset) ≤ B := by
    have hb := code.1
    have hc : 5 * containing.length ≤ B := metadata_le_wordLimit hcodePC
    omega
  let tested := runOps rom (scanBoundedTest 1 20 (start + 154)) before
  have htPC : tested.pc = 5 * (start + 154) := by
    rw [scanBoundedTest_pc rom CB q q 1 20 (start + 154) before
      ready.input.address ready.input.tools ready.tool_cell, Nat.sub_self, ite_eq_left rfl]
  have htActive : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  have testRun : natRun rom containing 9 before = tested :=
    stage_chunk_run rom containing start code .toolTest before ready.pc ready.active
  have testNumeric := scanBoundedTest_numeric rom B H CB M q q 1 20 (start + 154) before
    (fun reg => metadata_le_wordLimit (hr reg)) ready.input.address ready.input.tools ready.tool_cell
    (by decide) (by decide) qM qM (jump 154 (by decide)) room.1 hH
  have testSafe := stage_chunk_safe_at rom B H containing start code .toolTest before
    ready.pc ready.active testNumeric 154 (by decide) htPC
  change RunFacts B H rom containing 9 before at testSafe
  have testRegs : RegistersLE B tested := by
    have h := ((testSafe.1).final _ _ _ _ _).1
    rw [testRun] at h
    exact h
  let checked := runOps rom (stageNodeWriteTest (start + 180)) tested
  let matched := stageMatchTools rom reference.heap CB M stage.val node.val q
  have hcPC : checked.pc = if matched then 5 * (start + 159) else 5 * (start + 180) := by
    rw [stageNodeWriteTest_pc rom CB _ (start + 180) tested ready.input.address ready.match_cell, htPC]
    change (if bit matched = 0 then _ else _) = _
    cases matched <;> simp [bit]
    omega
  have hcActive : checked.halted = false := (runOps_halted rom _ tested).trans htActive
  have flagBound : bit matched ≤ B := by
    cases matched <;> simp [bit]
    omega
  have checkNumeric := stageNodeWriteTest_numeric rom B H CB M (bit matched) (start + 180)
    tested testRegs ready.input.address ready.match_cell flagBound (jump 180 (by decide)) room.1 hH
  have checkRun : natRun rom containing 5 tested = checked :=
    stage_chunk_run rom containing start code .writeTest tested htPC htActive
  have checkSafe : RunFacts B H rom containing 5 tested := by
    cases hm : matched
    · exact stage_chunk_safe_at rom B H containing start code .writeTest tested htPC htActive
        checkNumeric 180 (by decide) (by simpa only [stageChunkCode, checked, hm, Bool.false_eq_true, ite_false] using hcPC)
    · exact stage_chunk_safe_at rom B H containing start code .writeTest tested htPC htActive
        checkNumeric 159 (by decide) (by simpa only [stageChunkCode, checked, hm, ite_true] using hcPC)
  have checkRegs : RegistersLE B checked := by
    have h := ((checkSafe.1).final _ _ _ _ _).1
    rw [checkRun] at h
    exact h
  have checkedInput : ScanInput q full CB P checked :=
    ScanInput.of_frame ready.input layout (fun _ _ => rfl) ready.input.address
  let stored := if matched then runOps rom stageRecord checked else checked
  have below := stage_region_below_control q full CB P layout
  have hs := stage.isLt
  have hstage : fieldAddress P full.length (preparedSize q full) .stage stage.val < CB := by
    unfold fieldAddress fieldFactor fieldExtra at below ⊢
    omega
  have storedHeap : stored.heap = if matched then
      Function.update before.heap (fieldAddress P full.length (preparedSize q full) .stage stage.val)
        (node.val + 1) else before.heap := by
    by_cases hm : matched = true
    · simp only [stored, ite_eq_left hm]
      exact (stageRecord_effect rom CB P full.length (preparedSize q full) stage.val node.val checked
        ready.input.address ready.input.base ready.input.nodes ready.stage_cell ready.node_cell).2
    · simp only [stored, ite_eq_right hm]
      rfl
  have storedCB : stored.register .address = CB := by
    by_cases hm : matched = true
    · simp only [stored, ite_eq_left hm]
      exact ready.input.address
    · simp only [stored, ite_eq_right hm]
      exact ready.input.address
  have storedPC : stored.pc = 5 * (start + 180) := by
    by_cases hm : matched = true
    · simp only [stored, ite_eq_left hm]
      rw [runOps_pc rom _ checked (by simp [stageRecord, loadRel, storeField, fieldPointer,
        fieldPointerLead, fieldPointerExtra, NoJump]), hcPC, ite_eq_left hm,
        show stageRecord.length = 21 from rfl]
      omega
    · simpa only [stored, ite_eq_right hm] using hcPC
  have storedActive : stored.halted = false := by
    by_cases hm : matched = true
    · simpa only [stored, ite_eq_left hm] using (runOps_halted rom stageRecord checked).trans hcActive
    · simpa only [stored, ite_eq_right hm] using hcActive
  have storeRun : natRun rom containing (if matched then 21 else 0) checked = stored := by
    by_cases hm : matched = true
    · simp only [stored, ite_eq_left hm]
      exact stage_chunk_run rom containing start code .record checked
        (by simpa only [stageChunkOffset, ite_eq_left hm] using hcPC) hcActive
    · simp only [stored, ite_eq_right hm, natRun]
  have storeSafe : RunFacts B H rom containing (if matched then 21 else 0) checked := by
    by_cases hm : matched = true
    · simp only [ite_eq_left hm]
      have numeric := stageRecord_numeric q full B H CB P stage node checked checkedInput
        ready.stage_cell ready.node_cell checkRegs layout room.1 hH
      exact stage_chunk_safe_at rom B H containing start code .record checked
        (by simpa only [stageChunkOffset, ite_eq_left hm] using hcPC) hcActive numeric 180 (by decide)
        (by simpa only [stageChunkCode, stored, ite_eq_left hm] using storedPC)
    · simp only [ite_eq_right hm]
      constructor
      · constructor
        · intro count hcount
          have hz : count = 0 := by omega
          subst count
          refine ⟨checkRegs, hcActive, start + 180, by have hb := code.1; omega, ?_⟩
          simpa only [natRun, ite_eq_right hm] using hcPC
        · intro count hcount
          omega
      · intro count hcount
        have hz : count = 0 := by omega
        subst count
        rfl
  have storedRegs : RegistersLE B stored := by
    have h := ((storeSafe.1).final _ _ _ _ _).1
    rw [storeRun] at h
    exact h
  have storedNode : stored.heap (CB + 19) = node.val := by
    rw [storedHeap]
    split_ifs
    · rw [Function.update_of_ne (by omega)]
      exact ready.node_cell
    · exact ready.node_cell
  let after := runOps rom (stageNodeTail start) stored
  have tail := stageTail_effect rom CB node.val 19 (start + 34) stored storedCB storedNode
  have hh : after.heap = stageNodeFinishHeap q full reference CB P stage.val node.val before.heap := by
    change (runOps rom (PA06A19PrepareChildrenCache023.incrementRel 19 ++ jumpTo (start + 34)) stored).heap = _
    rw [tail.2.1, storedHeap]
    rfl
  have next := stage_node_finish_ready q full CB P reference stage node (5 * (start + 51)) (5 * (start + 34))
    before after ready layout hh tail.1 tail.2.2.1 ((tail.2.2.2).trans storedActive)
  have tailRun : natRun rom containing 11 stored = after :=
    stage_chunk_run rom containing start code .nodeTail stored storedPC storedActive
  have tailNumeric := stageTail_numeric rom B H CB M 19 node.val (start + 34) stored storedRegs
    storedCB storedNode (by decide) (by omega) (jump 34 (by decide)) room.1 hH
  have tailSafe := stage_chunk_safe_at rom B H containing start code .nodeTail stored storedPC storedActive
    tailNumeric 34 (by decide) tail.2.2.1
  change RunFacts B H rom containing 11 stored at tailSafe
  have headRun : natRun rom containing (9 + 5) before = checked := by
    rw [natRun_add rom containing 9 5 before, testRun, checkRun]
  have headSafe := RunFacts.add B H rom containing 9 5 before testSafe (by rw [testRun]; exact checkSafe)
  have storeHeadRun : natRun rom containing ((9 + 5) + (if matched then 21 else 0)) before = stored := by
    rw [natRun_add rom containing (9 + 5) (if matched then 21 else 0) before, headRun, storeRun]
  have storeHeadSafe := RunFacts.add B H rom containing (9 + 5) (if matched then 21 else 0) before
    headSafe (by rw [headRun]; exact storeSafe)
  have allSafe := RunFacts.add B H rom containing ((9 + 5) + (if matched then 21 else 0)) 11 before
    storeHeadSafe (by rw [storeHeadRun]; exact tailSafe)
  have actual : natRun rom containing ((9 + 5) + (if matched then 21 else 0) + 11) before = after := by
    rw [natRun_add rom containing ((9 + 5) + (if matched then 21 else 0)) 11 before, storeHeadRun, tailRun]
  refine ⟨(9 + 5) + (if matched then 21 else 0) + 11, by split_ifs <;> omega, rfl, ?_⟩
  rw [actual]
  exact ⟨next.1, next.2, allSafe⟩

theorem stage_node_actual_joint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (referenceData : RawCardData q full (actualControlBase q full) reference)
    (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)
    (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (ready : StageNodeReady q full (actualControlBase q full) (actualPackedWords q full)
      reference stage node.val (5 * (start + 34)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    ∃ clock ≤ 63 + 90 * q,
      let after := natRun (rawIncidenceROM q full) containing clock before
      StageNodeReady q full (actualControlBase q full) (actualPackedWords q full)
        reference stage (node.val + 1) (5 * (start + 34)) after ∧
      StageFrame q full (actualControlBase q full) (actualPackedWords q full) before after ∧
      RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
        (rawIncidenceROM q full) containing clock before := by
  let rom := rawIncidenceROM q full
  let bits := indexWidth 32 full.length q
  let B := metadataWordLimit bits
  let H := actualAllocation q full
  let CB := actualControlBase q full
  let P := actualPackedWords q full
  let initialized := natRun rom containing 17 before
  have initialization := stage_node_initialize q full CB P reference rfl containing start code stage node before ready
  have initSafe := stage_node_initialize_runFacts q full hq reference containing start code stage node before ready hr hcodePC
  have initRegs : RegistersFit bits initialized := by
    intro reg
    exact (((initSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
  obtain ⟨scanClock, scanBound, scanReady, scanFrame, scanSafe⟩ :=
    stage_inner_final_joint q full hq reference referenceData containing start code stage node initialized
      initialization.1 initRegs hcodePC
  let scanned := natRun rom containing scanClock initialized
  have scannedRegs : RegistersFit bits scanned := by
    intro reg
    exact (((scanSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
  obtain ⟨finishClock, finishBound, _finishNamed, finishReady, finishFrame, finishSafe⟩ :=
    stage_node_finish_joint q full hq reference containing start code stage node scanned scanReady scannedRegs hcodePC
  have headRun : natRun rom containing (17 + scanClock) before = scanned := by
    rw [natRun_add rom containing 17 scanClock before]
  have headSafe := RunFacts.add B H rom containing 17 scanClock before initSafe scanSafe
  have allSafe := RunFacts.add B H rom containing (17 + scanClock) finishClock before headSafe
    (by rw [headRun]; exact finishSafe)
  refine ⟨17 + scanClock + finishClock, by omega, ?_⟩
  refine ⟨?_, ?_, allSafe⟩
  · rw [natRun_add rom containing (17 + scanClock) finishClock before, headRun]
    exact finishReady
  · rw [natRun_add rom containing (17 + scanClock) finishClock before, headRun]
    exact (initialization.2.trans scanFrame).trans finishFrame

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
