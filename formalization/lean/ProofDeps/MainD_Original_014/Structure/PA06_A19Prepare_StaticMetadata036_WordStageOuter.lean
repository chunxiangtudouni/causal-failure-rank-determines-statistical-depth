module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordStageOuterNumeric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNVALIDATED complete nested loops for the unchanged202-op stage
producer. Each induction step consumes a joint witness, retaining
one clock for the semantic output, finite heap frame and RunFacts. Actual
setup, conditional records, guards and tails are included.
No separately selected existential semantic clock is used. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass actualPackedWords actualControlBase actualAllocation RunFacts)

/-- Exactly count candidate nodes of one actual stage, using the same concrete run for semantic values,
the write footprint, and every fetched-prefix bound. The exhausted outer
guard is deliberately left to the row finish below. -/
theorem stage_node_loop_joint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (referenceData : RawCardData q full (actualControlBase q full) reference)
    (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)
    (stage : Fin full.length) (before : NatState)
    (ready : StageNodeReady q full (actualControlBase q full) (actualPackedWords q full)
      reference stage 0 (5 * (start + 34)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length))
    (count : Nat) (hc : count ≤ preparedSize q full) :
    ∃ clock ≤ count * (63 + 90 * q),
      let after := natRun (rawIncidenceROM q full) containing clock before
      StageNodeReady q full (actualControlBase q full) (actualPackedWords q full)
        reference stage count (5 * (start + 34)) after ∧
      StageFrame q full (actualControlBase q full) (actualPackedWords q full) before after ∧
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
            start + 34, by have hb := code.1; omega, ready.pc⟩
        · intro clock hclock
          omega
      · intro clock hclock
        have hz : clock = 0 := by omega
        subst clock
        rfl
    exact ⟨0, by omega, ready,
      StageFrame.refl q full (actualControlBase q full) (actualPackedWords q full) before, zeroSafe⟩
  | succ count ih =>
    intro hc
    obtain ⟨previousClock, previousBound, previousReady, previousFrame, previousSafe⟩ := ih (by omega)
    let previous := natRun rom containing previousClock before
    have previousRegs : RegistersFit bits previous := by
      intro reg
      exact (((previousSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
    obtain ⟨rowClock, rowBound, rowReady, rowFrame, rowSafe⟩ :=
      stage_node_actual_joint q full hq reference referenceData containing start code
        stage ⟨count, by change count < preparedSize q full; omega⟩ previous previousReady previousRegs hcodePC
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

/-- One real row: 30 setup, all t same-clock node iterations, and20 finish. -/
theorem stage_row_actual_joint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (referenceData : RawCardData q full (actualControlBase q full) reference)
    (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)
    (stage : Fin full.length) (before : NatState)
    (ready : StageOuterReady q full (actualControlBase q full) (actualPackedWords q full)
      reference stage.val (5 * (start + 4)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    ∃ clock ≤ 50 + preparedSize q full * (63 + 90 * q),
      let after := natRun (rawIncidenceROM q full) containing clock before
      StageOuterReady q full (actualControlBase q full) (actualPackedWords q full)
        reference (stage.val + 1) (5 * (start + 4)) after ∧
      StageFrame q full (actualControlBase q full) (actualPackedWords q full) before after ∧
      RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
        (rawIncidenceROM q full) containing clock before := by
  let rom := rawIncidenceROM q full
  let bits := indexWidth 32 full.length q
  let B := metadataWordLimit bits
  let H := actualAllocation q full
  let CB := actualControlBase q full
  let P := actualPackedWords q full
  let initialized := natRun rom containing 30 before
  have initialization := stage_row_initialize q full CB P reference rfl containing start code stage before ready
  have initSafe := stage_row_initialize_runFacts q full hq reference containing start code stage before ready hr hcodePC
  have initRegs : RegistersFit bits initialized := by
    intro reg
    exact (((initSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
  obtain ⟨scanClock, scanBound, scanReady, scanFrame, scanSafe⟩ :=
    stage_node_loop_joint q full hq reference referenceData containing start code stage initialized
      initialization.1 initRegs hcodePC (preparedSize q full) le_rfl
  let scanned := natRun rom containing scanClock initialized
  have finish := stage_row_finish q full CB P reference rfl containing start code stage scanned scanReady
  have scannedRegs : RegistersFit bits scanned := by
    intro reg
    exact (((scanSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
  have finishSafe := stage_row_finish_runFacts q full hq reference containing start code stage scanned scanReady scannedRegs hcodePC
  have headRun : natRun rom containing (30 + scanClock) before = scanned := by
    rw [natRun_add rom containing 30 scanClock before]
  have headSafe := RunFacts.add B H rom containing 30 scanClock before initSafe scanSafe
  have allSafe := RunFacts.add B H rom containing (30 + scanClock) 20 before headSafe
    (by rw [headRun]; exact finishSafe)
  refine ⟨30 + scanClock + 20, by omega, ?_⟩
  refine ⟨?_, ?_, allSafe⟩
  · rw [natRun_add rom containing (30 + scanClock) 20 before, headRun]
    exact finish.1
  · rw [natRun_add rom containing (30 + scanClock) 20 before, headRun]
    exact (initialization.2.trans scanFrame).trans finish.2

/-- Exactly count actual stages, using the same concrete run for semantic values,
the write footprint, and every fetched-prefix bound. The exhausted outer
guard is deliberately left to the complete producer below. -/
theorem stage_outer_partial_joint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (referenceData : RawCardData q full (actualControlBase q full) reference)
    (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)
    (before : NatState)
    (ready : StageOuterReady q full (actualControlBase q full) (actualPackedWords q full)
      reference 0 (5 * (start + 4)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length))
    (count : Nat) (hc : count ≤ full.length) :
    ∃ clock ≤ count * (50 + preparedSize q full * (63 + 90 * q)),
      let after := natRun (rawIncidenceROM q full) containing clock before
      StageOuterReady q full (actualControlBase q full) (actualPackedWords q full)
        reference count (5 * (start + 4)) after ∧
      StageFrame q full (actualControlBase q full) (actualPackedWords q full) before after ∧
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
      StageFrame.refl q full (actualControlBase q full) (actualPackedWords q full) before, zeroSafe⟩
  | succ count ih =>
    intro hc
    obtain ⟨previousClock, previousBound, previousReady, previousFrame, previousSafe⟩ := ih (by omega)
    let previous := natRun rom containing previousClock before
    have previousRegs : RegistersFit bits previous := by
      intro reg
      exact (((previousSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
    obtain ⟨rowClock, rowBound, rowReady, rowFrame, rowSafe⟩ :=
      stage_row_actual_joint q full hq reference referenceData containing start code
        ⟨count, by omega⟩ previous previousReady previousRegs hcodePC
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

/-- Complete unchanged202 Nat run with one clock carrying exact original
stage IDs, finite frame, hardware CB and every-prefix safety. N=0 uses the
zero-stage induction and still executes the actual initialization/guard. -/
theorem stage_actual_joint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)
    (before : NatState)
    (input : ScanInput q full (actualControlBase q full) (actualPackedWords q full) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hpc : before.pc = 5 * start) (ha : before.halted = false)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    ∃ clock ≤ 13 + full.length * (50 + preparedSize q full * (63 + 90 * q)),
      let after := natRun (rawIncidenceROM q full) containing clock before
      ScanInput q full (actualControlBase q full) (actualPackedWords q full) after ∧
      (∀ stage : Fin full.length,
        after.heap (fieldAddress (actualPackedWords q full) full.length (preparedSize q full) .stage stage.val) =
          encodedNode (prepareNormalization q full).indexed
            ((IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage)) ∧
      StageFrame q full (actualControlBase q full) (actualPackedWords q full) before after ∧
      after.register .address = actualControlBase q full ∧
      after.pc = 5 * (start + 202) ∧ after.halted = false ∧
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
  let initialized := runOps rom stageInitialize before
  have initializeNumeric := stageSetRel_numeric rom B H CB M 22 0 before
    (fun reg => metadata_le_wordLimit (hr reg)) input.address (by decide) (by omega) room.1 hH
  have initializePC : initialized.pc = 5 * (start + 4) := by
    rw [runOps_pc rom _ before (by simp [stageInitialize, PA06A19PrepareChildrenCache023.setRel,
      PA06A19PrepareChildrenCache023.storeRel, NoJump]), hpc, show stageInitialize.length = 4 from rfl]
    omega
  have initializeSafe := stage_chunk_safe_at rom B H containing start code .initialize before
    (by simpa only [stageChunkOffset, Nat.add_zero] using hpc) ha initializeNumeric
    4 (by decide) initializePC
  change RunFacts B H rom containing 4 before at initializeSafe
  have initializeRun : natRun rom containing 4 before = initialized :=
    stage_chunk_run rom containing start code .initialize before
      (by simpa only [stageChunkOffset, Nat.add_zero] using hpc) ha
  have initializeRegs : RegistersFit bits initialized := by
    intro reg
    have h := (((initializeSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
    rw [initializeRun] at h
    exact h
  have hh : initialized.heap = Function.update before.heap (CB + 22) 0 := by
    simpa only [initialized, stageInitialize, input.address] using
      PA06A19PrepareChildrenCache023.setRel_heap rom 22 0 before
  have initializedCB : initialized.register .address = CB := input.address
  have initializeFrame : StageFrame q full CB P before initialized :=
    stage_control_frame q full CB P before initialized (Or.inr (Or.inr (Or.inl rfl))) hh
  have initializeActive : initialized.halted = false := (runOps_halted rom _ before).trans ha
  have ready : StageOuterReady q full CB P before 0 (5 * (start + 4)) initialized := by
    refine ⟨ScanInput.of_stageFrame input layout initializeFrame initializedCB,
      ?_, ?_, initializePC, initializeActive⟩
    · rw [hh, Function.update_self]
    · intro stage hs
      omega
  obtain ⟨scanClock, scanBound, scanReady, scanFrame, scanSafe⟩ :=
    stage_outer_partial_joint q full hq before input.raw containing start code initialized ready
      initializeRegs hcodePC full.length le_rfl
  let scanned := natRun rom containing scanClock initialized
  have scannedRegs : RegistersLE B scanned := ((scanSafe.1).final _ _ _ _ _).1
  have hNM : full.length ≤ M := by dsimp only [M, mass]; omega
  have exitBound : 5 * (start + 202) ≤ B := by
    have hb := code.1
    have hc : 5 * containing.length ≤ B := metadata_le_wordLimit hcodePC
    omega
  have finalNumeric := scanBoundedTest_numeric rom B H CB M full.length full.length
    0 22 (start + 202) scanned scannedRegs scanReady.input.address scanReady.input.stages
    scanReady.stage_cell (by decide) (by decide) hNM hNM exitBound room.1 hH
  let after := runOps rom (scanBoundedTest 0 22 (start + 202)) scanned
  have endPC : after.pc = 5 * (start + 202) := by
    rw [scanBoundedTest_pc rom CB full.length full.length 0 22 (start + 202) scanned
      scanReady.input.address scanReady.input.stages scanReady.stage_cell, Nat.sub_self, ite_eq_left rfl]
  have endActive : after.halted = false := (runOps_halted rom _ scanned).trans scanReady.active
  have finalSafe := stage_chunk_safe_at rom B H containing start code .stageTest scanned
    scanReady.pc scanReady.active finalNumeric 202 (by decide) endPC
  change RunFacts B H rom containing 9 scanned at finalSafe
  have finalRun : natRun rom containing 9 scanned = after :=
    stage_chunk_run rom containing start code .stageTest scanned scanReady.pc scanReady.active
  have endFrame : StageFrame q full CB P scanned after := fun _ _ => rfl
  have endHeap : after.heap = scanned.heap := rfl
  have afterInput : ScanInput q full CB P after :=
    ScanInput.of_stageFrame scanReady.input layout endFrame scanReady.input.address
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
  refine ⟨afterInput, ?_, (initializeFrame.trans scanFrame).trans endFrame,
    afterInput.address, endPC, endActive, allSafe⟩
  intro stage
  rw [endHeap]
  exact (scanReady.stages stage stage.isLt).trans (stageScan_original q full hq CB before input.raw stage)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
