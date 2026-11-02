module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordScanRowJoint

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED complete node loop for the unchanged191-op leaf/tool
producer. Each induction step consumes the joint row witness, retaining
one clock for the semantic output, finite heap frame and RunFacts. Actual
four-op initialization and the final nine-op exhausted guard are included.
No separately selected existential semantic clock is used. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass actualPackedWords actualControlBase actualAllocation RunFacts)

/-- Exactly count nodes, using the same concrete run for semantic values,
the write footprint, and every fetched-prefix bound. The exhausted outer
guard is deliberately left to the complete producer below. -/
theorem scan_outer_partial_joint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (referenceData : RawCardData q full (actualControlBase q full) reference)
    (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start)
    (before : NatState)
    (ready : LeafOuterReady q full (actualControlBase q full) (actualPackedWords q full)
      0 (5 * (start + 4)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length))
    (count : Nat) (hc : count ≤ preparedSize q full) :
    ∃ clock ≤ count * (67 + 116 * q),
      let after := natRun (rawIncidenceROM q full) containing clock before
      LeafOuterReady q full (actualControlBase q full) (actualPackedWords q full)
        count (5 * (start + 4)) after ∧
      ScanFrame q full (actualControlBase q full) (actualPackedWords q full) before after ∧
      RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
        (rawIncidenceROM q full) containing clock before := by
  let rom := rawIncidenceROM q full
  let bits := indexWidth 32 full.length q
  let B := metadataWordLimit bits
  let H := actualAllocation q full
  revert hc
  induction count with
  | zero =>
    intro _
    have zeroSafe : RunFacts B H rom containing 0 before := by
      constructor
      · constructor
        · intro clock hclock
          have hz : clock = 0 := by omega
          subst clock
          exact ⟨fun reg => metadata_le_wordLimit (hr reg), ready.active,
            start + 4, by have hb := code.1; omega, ready.pc⟩
        · intro clock hclock
          omega
      · intro clock hclock
        have hz : clock = 0 := by omega
        subst clock
        rfl
    exact ⟨0, by omega, ready,
      ScanFrame.refl q full (actualControlBase q full) (actualPackedWords q full) before, zeroSafe⟩
  | succ count ih =>
    intro hc
    obtain ⟨previousClock, previousBound, previousReady, previousFrame, previousSafe⟩ := ih (by omega)
    let previous := natRun rom containing previousClock before
    have previousRegs : RegistersFit bits previous := by
      intro reg
      exact (((previousSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
    obtain ⟨rowClock, rowBound, rowReady, rowFrame, rowSafe⟩ :=
      scan_row_joint q full hq reference referenceData containing start code
        ⟨count, by change count < preparedSize q full; omega⟩ previous previousReady previousRegs hcodePC
    have combined : RunFacts B H rom containing (previousClock + rowClock) before :=
      RunFacts.add B H rom containing previousClock rowClock before previousSafe rowSafe
    refine ⟨previousClock + rowClock, ?_, ?_⟩
    · rw [Nat.succ_mul]
      omega
    · refine ⟨?_, ?_, combined⟩
      · rw [natRun_add rom containing previousClock rowClock before]
        exact rowReady
      · rw [natRun_add rom containing previousClock rowClock before]
        exact previousFrame.trans rowFrame

/-- The full actual191 producer. The original raw cache/dimensions and
incoming register/PC bounds are the only data premises. Output semantics,
frame and safety are jointly proved at the one selected actual clock. -/
theorem leaf_tool_actual_joint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start)
    (before : NatState)
    (input : ScanInput q full (actualControlBase q full) (actualPackedWords q full) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hpc : before.pc = 5 * start) (ha : before.halted = false)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    ∃ clock ≤ 13 + preparedSize q full * (67 + 116 * q),
      let after := natRun (rawIncidenceROM q full) containing clock before
      ScanInput q full (actualControlBase q full) (actualPackedWords q full) after ∧
      (∀ node : (prepareNormalization q full).indexed.NodeId,
        after.heap (fieldAddress (actualPackedWords q full) full.length (preparedSize q full) .leaf node.val) =
          originalLeaf q full node) ∧
      (∀ tool : Fin q,
        after.heap (fieldAddress (actualPackedWords q full) full.length (preparedSize q full) .tool tool.val) =
          ((IndexedStaticMetadata.buildPositive q full hq).toolNodes.get tool).val + 1) ∧
      ScanFrame q full (actualControlBase q full) (actualPackedWords q full) before after ∧
      after.register .address = actualControlBase q full ∧
      after.pc = 5 * (start + 191) ∧ after.halted = false ∧
      RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
        (rawIncidenceROM q full) containing clock before := by
  let rom := rawIncidenceROM q full
  let bits := indexWidth 32 full.length q
  let B := metadataWordLimit bits
  let H := actualAllocation q full
  let CB := actualControlBase q full
  let P := actualPackedWords q full
  let M := mass q full
  have layout : CB = 4 + P + 4096 * (mass q full + preparedSize q full) := rfl
  have room := PA06A19PrepareChildrenCache023.highCacheEnd_actual_fits q full hq
  have hH : H ≤ B := metadata_le_wordLimit room.2.1
  let initialized := runOps rom scanInitialize before
  have initializeNumeric := cardsInitialize_numeric rom B H CB M before
    (fun reg => metadata_le_wordLimit (hr reg)) input.address room.1 hH
  have initializeSafe := scan_chunk_safe rom B H containing start code .«initialize» before
    (by simpa only [scanChunkOffset, Nat.add_zero] using hpc) ha initializeNumeric
  change RunFacts B H rom containing 4 before at initializeSafe
  have initializeRun : natRun rom containing 4 before = initialized :=
    scan_chunk_run rom containing start code .«initialize» before
      (by simpa only [scanChunkOffset, Nat.add_zero] using hpc) ha
  have initializeRegs : RegistersFit bits initialized := by
    intro reg
    have h := (((initializeSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
    rw [initializeRun] at h
    exact h
  have hh : initialized.heap = Function.update before.heap (CB + 19) 0 := by
    simpa only [initialized, scanInitialize, input.address] using
      PA06A19PrepareChildrenCache023.setRel_heap rom 19 0 before
  have initializedCB : initialized.register .address = CB := input.address
  have initializeFrame : ScanFrame q full CB P before initialized :=
    scan_control_frame q full CB P before initialized (Or.inl rfl) hh
  have initializePC : initialized.pc = 5 * (start + 4) := by
    rw [runOps_pc rom _ before (by
      simp [scanInitialize, PA06A19PrepareChildrenCache023.setRel,
        PA06A19PrepareChildrenCache023.storeRel, NoJump]), hpc, show scanInitialize.length = 4 from rfl]
    omega
  have initializeActive : initialized.halted = false := (runOps_halted rom _ before).trans ha
  have ready : LeafOuterReady q full CB P 0 (5 * (start + 4)) initialized := by
    refine ⟨ScanInput.of_frame input layout initializeFrame initializedCB,
      ?_, ?_, ?_, initializePC, initializeActive⟩
    · rw [hh, Function.update_self]
    · intro node hn
      omega
    · intro tool ht
      omega
  obtain ⟨scanClock, scanBound, scanReady, scanFrame, scanSafe⟩ :=
    scan_outer_partial_joint q full hq before input.raw containing start code initialized ready
      initializeRegs hcodePC (preparedSize q full) le_rfl
  let scanned := natRun rom containing scanClock initialized
  have scannedRegs : RegistersLE B scanned := ((scanSafe.1).final _ _ _ _ _).1
  have htM : preparedSize q full ≤ M := prepared_indexed_size_le q full
  have exitBound : 5 * (start + 191) ≤ B := by
    have hb := code.1
    have hc : 5 * containing.length ≤ B := metadata_le_wordLimit hcodePC
    omega
  have finalNumeric := scanBoundedTest_numeric rom B H CB M (preparedSize q full)
    (preparedSize q full) 2 19 (start + 191) scanned scannedRegs scanReady.input.address
    scanReady.input.nodes scanReady.node_cell (by decide) (by decide) htM htM exitBound room.1 hH
  have finalSafe := scan_chunk_safe rom B H containing start code .outerTest scanned
    scanReady.pc scanReady.active finalNumeric
  change RunFacts B H rom containing 9 scanned at finalSafe
  let after := runOps rom (scanBoundedTest 2 19 (start + 191)) scanned
  have finalRun : natRun rom containing 9 scanned = after :=
    scan_chunk_run rom containing start code .outerTest scanned scanReady.pc scanReady.active
  have endPC : after.pc = 5 * (start + 191) := by
    rw [scanBoundedTest_pc rom CB (preparedSize q full) (preparedSize q full) 2 19 (start + 191) scanned
      scanReady.input.address scanReady.input.nodes scanReady.node_cell, Nat.sub_self, ite_eq_left rfl]
  have endActive : after.halted = false := (runOps_halted rom _ scanned).trans scanReady.active
  have endFrame : ScanFrame q full CB P scanned after := fun _ _ => rfl
  have endHeap : after.heap = scanned.heap := rfl
  have afterInput : ScanInput q full CB P after :=
    ScanInput.of_frame scanReady.input layout endFrame scanReady.input.address
  have firstSafe := RunFacts.add B H rom containing 4 scanClock before initializeSafe
    (by rw [initializeRun]; exact scanSafe)
  have firstRun : natRun rom containing (4 + scanClock) before = scanned := by
    rw [natRun_add rom containing 4 scanClock before, initializeRun]
  have allSafe := RunFacts.add B H rom containing (4 + scanClock) 9 before firstSafe
    (by rw [firstRun]; exact finalSafe)
  have actual : natRun rom containing (4 + scanClock + 9) before = after := by
    rw [natRun_add rom containing (4 + scanClock) 9 before, firstRun, finalRun]
  refine ⟨4 + scanClock + 9, by omega, ?_⟩
  rw [actual]
  refine ⟨afterInput, ?_, ?_, (initializeFrame.trans scanFrame).trans endFrame,
    afterInput.address, endPC, endActive, allSafe⟩
  · intro node
    rw [endHeap]
    exact scanReady.leaves node node.isLt
  · intro tool
    rw [endHeap]
    have htool : singletonIndex q full tool < preparedSize q full :=
      (IndexedStaticMetadata.singletonNode q full tool).isLt
    have h := scanReady.tools tool htool
    simpa only [IndexedStaticMetadata.buildPositive_tool_get, singletonIndex] using h

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
