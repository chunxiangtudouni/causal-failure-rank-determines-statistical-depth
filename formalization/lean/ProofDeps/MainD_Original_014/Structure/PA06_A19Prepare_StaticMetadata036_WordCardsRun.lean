module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordCardsChunks

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED all-clock proof for the same84-op actual card/internal loop.
Every semantic CardsReady below is obtained from its existing Nat theorem
at exactly the same clock. No output or whole-run safety is a caller input. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass highCacheEnd actualPackedWords actualControlBase actualAllocation
    loadRel storeRel setRel RunFacts)

section Actual
variable (q : Nat) (full : List (Finset (Fin q))) (B H CB P : Nat)
  (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
  (hroom : highCacheEnd CB (mass q full) < H) (hH : H ≤ B)
  (containing : List PackingOp) (start : Nat) (code : CardsCodeAt containing start)
  (hcode : 5 * containing.length ≤ B)

include hlayout hroom hH code hcode

theorem cards_iteration_runFacts (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (ready : CardsReady q full CB P node.val (5 * (start + 4)) before) (hr : RegistersLE B before) :
    RunFacts B H (rawIncidenceROM q full) containing 80 before := by
  let rom := rawIncidenceROM q full
  have htM : preparedSize q full ≤ mass q full := prepared_indexed_size_le q full
  have hn : node.val < preparedSize q full := node.isLt
  have jump (offset : Nat) (ho : offset ≤ 84) : 5 * (start + offset) ≤ B := by
    have hb := code.1
    omega
  let tested := runOps rom (scanBoundedTest 2 19 (start + 84)) before
  have testNumeric := cardsTest_numeric rom B H CB (mass q full) (preparedSize q full) node.val
    (start + 84) before hr ready.input.address ready.input.nodes ready.node_cell htM
    (by omega) (jump 84 le_rfl) hroom hH
  have testSafe := cards_chunk_safe rom B H containing start code .test before ready.pc ready.active testNumeric
  change RunFacts B H rom containing 9 before at testSafe
  have testRun : natRun rom containing 9 before = tested :=
    cards_chunk_run rom containing start code .test before ready.pc ready.active
  have testRegs : RegistersLE B tested := by
    have h := ((testSafe.1).final _ _ _ _ _).1
    rw [testRun] at h
    exact h
  have testPC : tested.pc = 5 * (start + 13) := by
    rw [scanBoundedTest_pc rom CB (preparedSize q full) node.val 2 19 (start + 84) before
      ready.input.address ready.input.nodes ready.node_cell, ite_eq_right (by omega), ready.pc]
    omega
  have testActive : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  have testedHeap : tested.heap = before.heap := rfl
  have testedNode : tested.heap (CB + 19) = node.val := by
    rw [testedHeap]
    exact ready.node_cell
  have testedInput : ScanInput q full CB P tested :=
    ScanInput.of_frame ready.input hlayout (fun _ _ => rfl) ready.input.address
  let stored := runOps rom cardsBody tested
  have bodyNumeric := cardsBody_numeric q full B H CB P node tested testedInput testedNode
    testRegs hlayout hroom hH
  have bodySafe := cards_chunk_safe rom B H containing start code .body tested testPC testActive bodyNumeric
  change RunFacts B H rom containing 60 tested at bodySafe
  have bodyRun : natRun rom containing 60 tested = stored :=
    cards_chunk_run rom containing start code .body tested testPC testActive
  have storedRegs : RegistersLE B stored := by
    have h := ((bodySafe.1).final _ _ _ _ _).1
    rw [bodyRun] at h
    exact h
  have body := cardsBody_effect q full CB P node tested testedInput testedNode hlayout
  have below := cards_regions_below_control q full CB P hlayout
  have hcard : fieldAddress P full.length (preparedSize q full) .cardinality node.val < CB := by
    simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
    omega
  have hint : fieldAddress P full.length (preparedSize q full) .internal node.val < CB := by
    simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
    omega
  have bodyHeap : stored.heap = Function.update
      (Function.update before.heap (fieldAddress P full.length (preparedSize q full) .cardinality node.val)
        ((prepareNormalization q full).indexed.metadata.cardinalities.get node))
      (fieldAddress P full.length (preparedSize q full) .internal node.val)
        (bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)) := by
    simpa only [testedHeap] using body.2
  have storedNode : stored.heap (CB + 19) = node.val := by
    rw [bodyHeap, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact ready.node_cell
  have storedPC : stored.pc = 5 * (start + 73) := by
    rw [runOps_pc rom _ tested cardsBody_noJump, testPC, cardsBody_length]
    omega
  have storedActive : stored.halted = false := (runOps_halted rom _ tested).trans testActive
  have tailNumeric := cardsTail_numeric rom B H CB (mass q full) node.val start stored
    storedRegs body.1 storedNode (by omega) (jump 4 (by decide)) hroom hH
  have tailSafe := cards_chunk_safe rom B H containing start code .tail stored storedPC storedActive tailNumeric
  change RunFacts B H rom containing 11 stored at tailSafe
  have headSafe := RunFacts.add B H rom containing 9 60 before testSafe (by rw [testRun]; exact bodySafe)
  have headRun : natRun rom containing (9 + 60) before = stored := by
    rw [natRun_add rom containing 9 60 before, testRun, bodyRun]
  exact RunFacts.add B H rom containing (9 + 60) 11 before headSafe (by rw [headRun]; exact tailSafe)

theorem cards_scan_partial_runFacts (before : NatState)
    (ready : CardsReady q full CB P 0 (5 * (start + 4)) before) (hr : RegistersLE B before)
    (count : Nat) (hc : count ≤ preparedSize q full) :
    RunFacts B H (rawIncidenceROM q full) containing (80 * count) before := by
  revert hc
  induction count with
  | zero =>
    intro _
    constructor
    · constructor
      · intro clock hc
        have hz : clock = 0 := by omega
        subst clock
        exact ⟨hr, ready.active, start + 4, by have hb := code.1; omega, ready.pc⟩
      · intro clock hc
        omega
    · intro clock hc
      have hz : clock = 0 := by omega
      subst clock
      rfl
  | succ count ih =>
    intro hc
    have safe := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing (80 * count) before
    have previousReady := (cards_scan_partial q full CB P hlayout containing start code before ready count (by omega)).1
    have previousRegs := ((safe.1).final _ _ _ _ _).1
    have within : count < preparedSize q full := by omega
    have next := cards_iteration_runFacts q full B H CB P hlayout hroom hH containing start code hcode
      ⟨count, within⟩ previous previousReady previousRegs
    rw [Nat.mul_succ]
    exact RunFacts.add B H (rawIncidenceROM q full) containing (80 * count) 80 before safe next

/-- The original exact13+80t Nat clock, strengthened with every fetched
prefix bound and hardwareCB preservation. This is a result, not a premise. -/
theorem cards_build_runFacts (before : NatState) (input : ScanInput q full CB P before)
    (hr : RegistersLE B before) (hpc : before.pc = 5 * start) (ha : before.halted = false) :
    RunFacts B H (rawIncidenceROM q full) containing (13 + 80 * preparedSize q full) before := by
  let rom := rawIncidenceROM q full
  let initialized := runOps rom (setRel 19 0) before
  have initializeNumeric := cardsInitialize_numeric rom B H CB (mass q full) before hr input.address hroom hH
  have initializeSafe := cards_chunk_safe rom B H containing start code .initialize before
    (by simpa only [cardsChunkOffset, Nat.add_zero] using hpc) ha initializeNumeric
  change RunFacts B H rom containing 4 before at initializeSafe
  have initializeRun : natRun rom containing 4 before = initialized :=
    cards_chunk_run rom containing start code .initialize before (by simpa only [cardsChunkOffset, Nat.add_zero] using hpc) ha
  have initializeRegs : RegistersLE B initialized := by
    have h := ((initializeSafe.1).final _ _ _ _ _).1
    rw [initializeRun] at h
    exact h
  have hh : initialized.heap = Function.update before.heap (CB + 19) 0 := by
    simpa only [initialized, input.address] using PA06A19PrepareChildrenCache023.setRel_heap rom 19 0 before
  have frame : CardsFrame q full CB P before initialized := by
    intro address hn
    have h19 : address ≠ CB + 19 := by unfold CardsAllowed at hn; omega
    rw [hh, Function.update_of_ne h19]
  have initPC : initialized.pc = 5 * (start + 4) := by
    have initializeLength : (setRel 19 0).length = 4 := rfl
    rw [runOps_pc rom _ before (by simp [setRel, storeRel, NoJump]), initializeLength, hpc]
    omega
  have initActive : initialized.halted = false := (runOps_halted rom _ before).trans ha
  have ready : CardsReady q full CB P 0 (5 * (start + 4)) initialized := by
    refine ⟨ScanInput.of_cardsFrame input hlayout frame input.address, ?_, ?_, initPC, initActive⟩
    · rw [hh, Function.update_self]
    · intro node hn
      omega
  have scanSafe := cards_scan_partial_runFacts q full B H CB P hlayout hroom hH containing start code hcode
    initialized ready initializeRegs (preparedSize q full) le_rfl
  let scanned := natRun rom containing (80 * preparedSize q full) initialized
  have scannedReady := (cards_scan_partial q full CB P hlayout containing start code initialized ready
    (preparedSize q full) le_rfl).1
  have scannedRegs := ((scanSafe.1).final _ _ _ _ _).1
  have htM : preparedSize q full ≤ mass q full := prepared_indexed_size_le q full
  have exitBound : 5 * (start + 84) ≤ B := by have hb := code.1; omega
  have testNumeric := cardsTest_numeric rom B H CB (mass q full) (preparedSize q full)
    (preparedSize q full) (start + 84) scanned scannedRegs scannedReady.input.address
    scannedReady.input.nodes scannedReady.node_cell htM htM exitBound hroom hH
  have testSafe := cards_chunk_safe rom B H containing start code .test scanned scannedReady.pc scannedReady.active testNumeric
  change RunFacts B H rom containing 9 scanned at testSafe
  have later := RunFacts.add B H rom containing (80 * preparedSize q full) 9 initialized scanSafe testSafe
  have all := RunFacts.add B H rom containing 4 (80 * preparedSize q full + 9) before initializeSafe
    (by rw [initializeRun]; exact later)
  have clock : 13 + 80 * preparedSize q full = 4 + (80 * preparedSize q full + 9) := by omega
  rw [clock]
  exact all

end Actual

/-- Original common32/8192 factory discharges every local range/room fact.
The input contains only actual copied raw cells and permanent dimensions. -/
theorem cards_actual_runFacts (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (containing : List PackingOp) (start : Nat) (code : CardsCodeAt containing start)
    (before : NatState) (input : ScanInput q full (actualControlBase q full) (actualPackedWords q full) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hpc : before.pc = 5 * start) (ha : before.halted = false)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
      (rawIncidenceROM q full) containing (13 + 80 * preparedSize q full) before := by
  have room := PA06A19PrepareChildrenCache023.highCacheEnd_actual_fits q full hq
  exact cards_build_runFacts q full (metadataWordLimit (indexWidth 32 full.length q))
    (actualAllocation q full) (actualControlBase q full) (actualPackedWords q full) rfl
    room.1 (metadata_le_wordLimit room.2.1) containing start code (metadata_le_wordLimit hcodePC)
    before input (fun reg => metadata_le_wordLimit (hr reg)) hpc ha

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
