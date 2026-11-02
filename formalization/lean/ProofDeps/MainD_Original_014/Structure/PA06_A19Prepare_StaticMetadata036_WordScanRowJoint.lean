module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordScanInner

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED one-row joint witness for the unchanged191-op scanner.
Actual47 initialization, the same-clock q-tool joint scan, and actual20
finish share one Nat execution. Deterministic existing47/20 semantic APIs
are reused; no opaque existential row or semantic clock is selected.
This does not aggregate the node loop or the202 stage producer. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass actualPackedWords actualControlBase actualAllocation RunFacts)

private theorem scan_row_initialize_runFacts (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start)
    (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (ready : LeafOuterReady q full (actualControlBase q full) (actualPackedWords q full)
      node.val (5 * (start + 4)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
      (rawIncidenceROM q full) containing 47 before := by
  let rom := rawIncidenceROM q full
  let bits := indexWidth 32 full.length q
  let B := metadataWordLimit bits
  let H := actualAllocation q full
  let CB := actualControlBase q full
  let P := actualPackedWords q full
  let M := mass q full
  have room := PA06A19PrepareChildrenCache023.highCacheEnd_actual_fits q full hq
  have hH : H ≤ B := metadata_le_wordLimit room.2.1
  have regs : RegistersLE B before := fun reg => metadata_le_wordLimit (hr reg)
  have htM : preparedSize q full ≤ M := prepared_indexed_size_le q full
  have hn : node.val < preparedSize q full := node.isLt
  have exitBound : 5 * (start + 191) ≤ B := by
    have hb := code.1
    have hc : 5 * containing.length ≤ B := metadata_le_wordLimit hcodePC
    omega
  let tested := runOps rom (scanBoundedTest 2 19 (start + 191)) before
  have testNumeric := scanBoundedTest_numeric rom B H CB M (preparedSize q full) node.val
    2 19 (start + 191) before regs ready.input.address ready.input.nodes ready.node_cell
    (by decide) (by decide) htM (by omega) exitBound room.1 hH
  have testSafe := scan_chunk_safe rom B H containing start code .outerTest before
    ready.pc ready.active testNumeric
  change RunFacts B H rom containing 9 before at testSafe
  have testRun : natRun rom containing 9 before = tested :=
    scan_chunk_run rom containing start code .outerTest before ready.pc ready.active
  have testRegs : RegistersLE B tested := by
    have h := ((testSafe.1).final _ _ _ _ _).1
    rw [testRun] at h
    exact h
  have testPC : tested.pc = 5 * (start + 13) := by
    rw [scanBoundedTest_pc rom CB (preparedSize q full) node.val 2 19 (start + 191) before
      ready.input.address ready.input.nodes ready.node_cell, ite_eq_right (by omega), ready.pc]
    omega
  have testActive : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  have testedInput : ScanInput q full CB P tested :=
    ScanInput.of_frame ready.input rfl (fun _ _ => rfl) ready.input.address
  have initializeSafe := scanRowInitialize_runFacts q full B H CB P containing start code node tested
    testedInput ready.node_cell testRegs rfl room.1 hH testPC testActive
  exact RunFacts.add B H rom containing 9 38 before testSafe (by rw [testRun]; exact initializeSafe)

private theorem scan_row_finish_runFacts (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start)
    (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (ready : LeafInnerReady q full (actualControlBase q full) (actualPackedWords q full)
      reference node q (5 * (start + 51)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
      (rawIncidenceROM q full) containing 20 before := by
  let rom := rawIncidenceROM q full
  let bits := indexWidth 32 full.length q
  let B := metadataWordLimit bits
  let H := actualAllocation q full
  let CB := actualControlBase q full
  let M := mass q full
  have room := PA06A19PrepareChildrenCache023.highCacheEnd_actual_fits q full hq
  have hH : H ≤ B := metadata_le_wordLimit room.2.1
  have regs : RegistersLE B before := fun reg => metadata_le_wordLimit (hr reg)
  have htM : preparedSize q full ≤ M := prepared_indexed_size_le q full
  have hn : node.val < preparedSize q full := node.isLt
  have qM : q ≤ M := by dsimp only [M, mass]; omega
  have jump (offset : Nat) (ho : offset ≤ 191) : 5 * (start + offset) ≤ B := by
    have hb := code.1
    have hc : 5 * containing.length ≤ B := metadata_le_wordLimit hcodePC
    omega
  let tested := runOps rom (scanBoundedTest 1 20 (start + 180)) before
  have testNumeric := scanBoundedTest_numeric rom B H CB M q q 1 20 (start + 180) before
    regs ready.input.address ready.input.tools ready.tool_cell (by decide) (by decide) qM qM
    (jump 180 (by decide)) room.1 hH
  have testSafe := scan_chunk_safe rom B H containing start code .innerTest before
    ready.pc ready.active testNumeric
  change RunFacts B H rom containing 9 before at testSafe
  have testRun : natRun rom containing 9 before = tested :=
    scan_chunk_run rom containing start code .innerTest before ready.pc ready.active
  have testRegs : RegistersLE B tested := by
    have h := ((testSafe.1).final _ _ _ _ _).1
    rw [testRun] at h
    exact h
  have testPC : tested.pc = 5 * (start + 180) := by
    rw [scanBoundedTest_pc rom CB q q 1 20 (start + 180) before
      ready.input.address ready.input.tools ready.tool_cell, Nat.sub_self, ite_eq_left rfl]
  have testActive : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  have tailNumeric : NumericSafe B H rom (scanOuterTail start) tested :=
    cardsTail_numeric rom B H CB M node.val start tested testRegs ready.input.address ready.node_cell
      (by omega) (jump 4 (by decide)) room.1 hH
  have tailSafe := scan_chunk_safe rom B H containing start code .outerTail tested testPC testActive tailNumeric
  change RunFacts B H rom containing 11 tested at tailSafe
  exact RunFacts.add B H rom containing 9 11 before testSafe (by rw [testRun]; exact tailSafe)

/-- One row returns the original next-node outer invariant at PC4, with
its real heap frame and all-prefix safety at the SAME selected clock. -/
theorem scan_row_joint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (referenceData : RawCardData q full (actualControlBase q full) reference)
    (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start)
    (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (ready : LeafOuterReady q full (actualControlBase q full) (actualPackedWords q full)
      node.val (5 * (start + 4)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    ∃ clock ≤ 67 + 116 * q,
      let after := natRun (rawIncidenceROM q full) containing clock before
      LeafOuterReady q full (actualControlBase q full) (actualPackedWords q full)
        (node.val + 1) (5 * (start + 4)) after ∧
      ScanFrame q full (actualControlBase q full) (actualPackedWords q full) before after ∧
      RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
        (rawIncidenceROM q full) containing clock before := by
  let rom := rawIncidenceROM q full
  let bits := indexWidth 32 full.length q
  let B := metadataWordLimit bits
  let H := actualAllocation q full
  let CB := actualControlBase q full
  let P := actualPackedWords q full
  let initialized := natRun rom containing 47 before
  have initialization := leaf_row_initialize q full CB P reference rfl containing start code node before ready
  have initializeSafe := scan_row_initialize_runFacts q full hq containing start code node before ready hr hcodePC
  have initializeRegs : RegistersFit bits initialized := by
    intro reg
    exact (((initializeSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
  obtain ⟨innerClock, innerBound, innerReady, innerFrame, innerSafe⟩ :=
    scan_inner_final_joint q full hq reference referenceData containing start code node initialized
      initialization.1 initializeRegs hcodePC
  let scanned := natRun rom containing innerClock initialized
  have finish := leaf_row_finish q full CB P reference referenceData rfl containing start code node scanned innerReady
  have scannedRegs : RegistersFit bits scanned := by
    intro reg
    exact (((innerSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
  have finishSafe := scan_row_finish_runFacts q full hq reference containing start code node scanned
    innerReady scannedRegs hcodePC
  have headSafe := RunFacts.add B H rom containing 47 innerClock before initializeSafe innerSafe
  have headRun : natRun rom containing (47 + innerClock) before = scanned := by
    rw [natRun_add rom containing 47 innerClock before]
  have allSafe := RunFacts.add B H rom containing (47 + innerClock) 20 before headSafe
    (by rw [headRun]; exact finishSafe)
  refine ⟨47 + innerClock + 20, by omega, ?_⟩
  refine ⟨?_, ?_, allSafe⟩
  · rw [natRun_add rom containing (47 + innerClock) 20 before, headRun]
    exact finish.1
  · rw [natRun_add rom containing (47 + innerClock) 20 before, headRun]
    exact (initialization.2.trans innerFrame).trans finish.2

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
