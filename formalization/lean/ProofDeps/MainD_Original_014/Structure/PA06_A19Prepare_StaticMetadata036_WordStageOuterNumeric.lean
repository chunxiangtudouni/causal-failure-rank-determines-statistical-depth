module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordStageNodeJoint
public import Structure.PA06_A19Prepare_StaticMetadata036_StageRun

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNVALIDATED actual row setup/finish numeric and fetched-prefix facts.
Every clock is the fixed short concrete chunk clock used by Nat semantics. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass highCacheEnd loadRel storeRel setRel actualPackedWords actualControlBase actualAllocation RunFacts)

def stageRowZeroHead : List PackingOp :=
  loadRel .old 22 ++ [.base (.base (.constant .value 0))]

theorem stageRowInitialize_numeric (q : Nat) (full : List (Finset (Fin q))) (B H CB P : Nat)
    (stage : Fin full.length) (state : NatState) (input : ScanInput q full CB P state)
    (hs : state.heap (CB + 22) = stage.val) (hr : RegistersLE B state)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hroom : highCacheEnd CB (mass q full) < H) (hH : H ≤ B) :
    NumericSafe B H (rawIncidenceROM q full) stageRowInitialize state := by
  let rom := rawIncidenceROM q full
  have hCB : state.register .address = CB := input.address
  have hstage := stage.isLt
  have hNM : full.length ≤ mass q full := by unfold mass; omega
  have headSafe : NumericSafe B H rom stageRowZeroHead state := by
    constructor
    · intro count hc reg
      have hreg := hr reg
      change count ≤ 4 at hc
      interval_cases count <;> cases reg <;>
        simp_all [stageRowZeroHead, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals unfold highCacheEnd at hroom; omega
    · intro count hc
      change count < 4 at hc
      interval_cases count <;>
        simp_all [stageRowZeroHead, loadRel, runOps, natExecuteOp, Op.execute,
          Instruction.execute, NatAccessFits, AccessFits]
      all_goals unfold highCacheEnd at hroom; omega
  let head := runOps rom stageRowZeroHead state
  have effect : head.register .address = CB ∧ head.register .old = stage.val ∧ head.heap = state.heap := by
    simp [head, stageRowZeroHead, loadRel, runOps, natExecuteOp, Op.execute,
      Instruction.execute, hCB, hs]
  have storeSafe := storeField_numeric rom B H CB P full.length q (preparedSize q full)
    stage.val .stage head (headSafe.final _ _ _ _ _) effect.1 input.base input.nodes input.stages
    effect.2.1 stage.isLt hlayout (by unfold highCacheEnd at hroom; omega) hH
  let zeroed := runOps rom (storeField .stage) head
  have zeroCB : zeroed.register .address = CB :=
    (storeField_effect rom CB P full.length (preparedSize q full) stage.val .stage head
      effect.1 input.base input.nodes input.stages effect.2.1).1
  have initializeSafe := stageSetRel_numeric rom B H CB (mass q full) 19 0 zeroed
    (storeSafe.final _ _ _ _ _) zeroCB (by decide) (by omega) hroom hH
  have first := NumericSafe.append B H rom stageRowZeroHead (storeField .stage) state headSafe storeSafe
  change NumericSafe B H rom ((stageRowZeroHead ++ storeField .stage) ++ setRel 19 0) state
  exact NumericSafe.append B H rom (stageRowZeroHead ++ storeField .stage) (setRel 19 0) state first
    (by rw [runOps_append]; exact initializeSafe)

theorem stage_row_initialize_runFacts (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)
    (stage : Fin full.length) (before : NatState)
    (ready : StageOuterReady q full (actualControlBase q full) (actualPackedWords q full)
      reference stage.val (5 * (start + 4)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
      (rawIncidenceROM q full) containing 30 before := by
  let rom := rawIncidenceROM q full
  let B := metadataWordLimit (indexWidth 32 full.length q)
  let H := actualAllocation q full
  let CB := actualControlBase q full
  let P := actualPackedWords q full
  let M := mass q full
  have room := PA06A19PrepareChildrenCache023.highCacheEnd_actual_fits q full hq
  have hH : H ≤ B := metadata_le_wordLimit room.2.1
  have hNM : full.length ≤ M := by dsimp only [M, mass]; omega
  have hs := stage.isLt
  have exitBound : 5 * (start + 202) ≤ B := by
    have hb := code.1
    have hc := metadata_le_wordLimit hcodePC
    omega
  let tested := runOps rom (scanBoundedTest 0 22 (start + 202)) before
  have testPC : tested.pc = 5 * (start + 13) := by
    rw [scanBoundedTest_pc rom CB full.length stage.val 0 22 (start + 202) before
      ready.input.address ready.input.stages ready.stage_cell, ite_eq_right (by omega), ready.pc]
    omega
  have testActive : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  have testNumeric := scanBoundedTest_numeric rom B H CB M full.length stage.val 0 22 (start + 202) before
    (fun reg => metadata_le_wordLimit (hr reg)) ready.input.address ready.input.stages ready.stage_cell
    (by decide) (by decide) hNM (by omega) exitBound room.1 hH
  have testSafe := stage_chunk_safe_at rom B H containing start code .stageTest before
    ready.pc ready.active testNumeric 13 (by decide) testPC
  change RunFacts B H rom containing 9 before at testSafe
  have testRun : natRun rom containing 9 before = tested :=
    stage_chunk_run rom containing start code .stageTest before ready.pc ready.active
  have testRegs : RegistersLE B tested := by
    have h := ((testSafe.1).final _ _ _ _ _).1
    rw [testRun] at h
    exact h
  have testedInput : ScanInput q full CB P tested :=
    ScanInput.of_frame ready.input rfl (fun _ _ => rfl) ready.input.address
  have initNumeric := stageRowInitialize_numeric q full B H CB P stage tested testedInput
    ready.stage_cell testRegs rfl room.1 hH
  have initPC : (runOps rom stageRowInitialize tested).pc = 5 * (start + 34) := by
    rw [runOps_pc rom _ tested (by simp [stageRowInitialize, loadRel, storeField, fieldPointer,
      fieldPointerLead, fieldPointerExtra, setRel, storeRel, NoJump]), testPC,
      show stageRowInitialize.length = 21 from rfl]
    omega
  have initSafe := stage_chunk_safe_at rom B H containing start code .rowInitialize tested
    testPC testActive initNumeric 34 (by decide) initPC
  change RunFacts B H rom containing 21 tested at initSafe
  exact RunFacts.add B H rom containing 9 21 before testSafe (by rw [testRun]; exact initSafe)

theorem stage_row_finish_runFacts (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)
    (stage : Fin full.length) (before : NatState)
    (ready : StageNodeReady q full (actualControlBase q full) (actualPackedWords q full)
      reference stage (preparedSize q full) (5 * (start + 34)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
      (rawIncidenceROM q full) containing 20 before := by
  let rom := rawIncidenceROM q full
  let B := metadataWordLimit (indexWidth 32 full.length q)
  let H := actualAllocation q full
  let CB := actualControlBase q full
  let M := mass q full
  have room := PA06A19PrepareChildrenCache023.highCacheEnd_actual_fits q full hq
  have hH : H ≤ B := metadata_le_wordLimit room.2.1
  have htM : preparedSize q full ≤ M := prepared_indexed_size_le q full
  have hNM : full.length ≤ M := by dsimp only [M, mass]; omega
  have hs := stage.isLt
  have jump (offset : Nat) (ho : offset ≤ 202) : 5 * (start + offset) ≤ B := by
    have hb := code.1
    have hc := metadata_le_wordLimit hcodePC
    omega
  let tested := runOps rom (scanBoundedTest 2 19 (start + 191)) before
  have testPC : tested.pc = 5 * (start + 191) := by
    rw [scanBoundedTest_pc rom CB (preparedSize q full) (preparedSize q full) 2 19 (start + 191) before
      ready.input.address ready.input.nodes ready.node_cell, Nat.sub_self, ite_eq_left rfl]
  have testActive : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  have testNumeric := scanBoundedTest_numeric rom B H CB M (preparedSize q full) (preparedSize q full)
    2 19 (start + 191) before (fun reg => metadata_le_wordLimit (hr reg))
    ready.input.address ready.input.nodes ready.node_cell (by decide) (by decide)
    htM htM (jump 191 (by decide)) room.1 hH
  have testSafe := stage_chunk_safe_at rom B H containing start code .nodeTest before
    ready.pc ready.active testNumeric 191 (by decide) testPC
  change RunFacts B H rom containing 9 before at testSafe
  have testRun : natRun rom containing 9 before = tested :=
    stage_chunk_run rom containing start code .nodeTest before ready.pc ready.active
  have testRegs : RegistersLE B tested := by
    have h := ((testSafe.1).final _ _ _ _ _).1
    rw [testRun] at h
    exact h
  have tail := stageTail_effect rom CB stage.val 22 (start + 4) tested ready.input.address ready.stage_cell
  have tailNumeric := stageTail_numeric rom B H CB M 22 stage.val (start + 4) tested testRegs
    ready.input.address ready.stage_cell (by decide) (by omega) (jump 4 (by decide)) room.1 hH
  have tailSafe := stage_chunk_safe_at rom B H containing start code .outerTail tested
    testPC testActive tailNumeric 4 (by decide) tail.2.2.1
  change RunFacts B H rom containing 11 tested at tailSafe
  exact RunFacts.add B H rom containing 9 11 before testSafe (by rw [testRun]; exact tailSafe)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
