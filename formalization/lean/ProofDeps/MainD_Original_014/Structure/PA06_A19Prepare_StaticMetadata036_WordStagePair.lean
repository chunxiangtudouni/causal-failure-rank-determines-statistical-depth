module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordStageChunks
public import Structure.PA06_A19Prepare_StaticMetadata036_WordQueryExact

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED one actual tool comparison of the unchanged202-op stage
producer. Its named clock uses the actual heap after guard/read/arguments;
the real frozen022 query executes at precisely nodeReadClock, not a chosen
returning clock. One witness carries semantics, finite frame and RunFacts.
No stage map or whole-run safety oracle is an input. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass loadRel storeRel actualPackedWords actualControlBase actualAllocation RunFacts)

/-- The query source heap is the real output of the actual finite prefix.
This does not supply a stage answer, skip the raw read, or reset any state. -/
def stagePairClock (q : Nat) (full : List (Finset (Fin q))) (CB start : Nat)
    (before : NatState) (node tool : Nat) : Nat :=
  let rom := rawIncidenceROM q full
  let tested := runOps rom (scanBoundedTest 1 20 (start + 154)) before
  let rawRead := runOps rom stageRead tested
  let arguments := runOps rom scanArguments rawRead
  9 + 17 + 6 + nodeReadClock full.length arguments.heap CB (mass q full) node tool + 14 + 11

theorem stagePairClock_le (q : Nat) (full : List (Finset (Fin q))) (CB start : Nat)
    (before : NatState) (node tool : Nat) : stagePairClock q full CB start before node tool ≤ 90 := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (scanBoundedTest 1 20 (start + 154)) before
  let rawRead := runOps rom stageRead tested
  let arguments := runOps rom scanArguments rawRead
  have hc := nodeReadClock_le full.length arguments.heap CB (mass q full) node tool
  change 9 + 17 + 6 + nodeReadClock full.length arguments.heap CB (mass q full) node tool + 14 + 11 ≤ 90
  omega

/-- Exactly one real stage/node/tool comparison. The same selected clock
advances the streaming equality flag, preserves the finite stage frame,
and certifies every fetched prefix on the original common32/8192 heap.
Only current loop invariants and actual copied raw cells are consumed. -/
theorem stage_pair_actual_joint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (referenceData : RawCardData q full (actualControlBase q full) reference)
    (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)
    (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId)
    (tool : Fin q) (before : NatState)
    (ready : StageToolReady q full (actualControlBase q full) (actualPackedWords q full)
      reference stage node tool.val (5 * (start + 51)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    ∃ clock ≤ 90,
      clock = stagePairClock q full (actualControlBase q full) start before node.val tool.val ∧
      let after := natRun (rawIncidenceROM q full) containing clock before
      StageToolReady q full (actualControlBase q full) (actualPackedWords q full)
        reference stage node (tool.val + 1) (5 * (start + 51)) after ∧
      StageFrame q full (actualControlBase q full) (actualPackedWords q full) before after ∧
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
  have regs : RegistersLE B before := fun reg => metadata_le_wordLimit (hr reg)
  have htM : preparedSize q full ≤ M := prepared_indexed_size_le q full
  have hn : node.val < preparedSize q full := node.isLt
  have hj := tool.isLt
  have qM : q ≤ M := by dsimp only [M, mass]; omega
  have jump (offset : Nat) (ho : offset ≤ 202) : 5 * (start + offset) ≤ B := by
    have hb := code.1
    have hc : 5 * containing.length ≤ B := metadata_le_wordLimit hcodePC
    omega
  let tested := runOps rom (scanBoundedTest 1 20 (start + 154)) before
  have testPC : tested.pc = 5 * (start + 60) := by
    rw [scanBoundedTest_pc rom CB q tool.val 1 20 (start + 154) before
      ready.input.address ready.input.tools ready.tool_cell, ite_eq_right (by omega), ready.pc]
    omega
  have testActive : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  have testRun : natRun rom containing 9 before = tested :=
    stage_chunk_run rom containing start code .toolTest before ready.pc ready.active
  have testNumeric := scanBoundedTest_numeric rom B H CB M q tool.val 1 20 (start + 154) before
    regs ready.input.address ready.input.tools ready.tool_cell (by decide) (by decide) qM (by omega)
    (jump 154 (by decide)) room.1 hH
  have testSafe := stage_chunk_safe_at rom B H containing start code .toolTest before
    ready.pc ready.active testNumeric 60 (by decide) testPC
  change RunFacts B H rom containing 9 before at testSafe
  have testRegs : RegistersLE B tested := by
    have h := ((testSafe.1).final _ _ _ _ _).1
    rw [testRun] at h
    exact h
  let rawRead := runOps rom stageRead tested
  have raw := stageRead_effect rom CB stage.val tool.val q tested ready.input.address ready.stage_cell
    ready.tool_cell ready.input.tools (raw_header_q q full)
  have rawHeap : rawRead.heap = Function.update before.heap (CB + 24) (rawStageBit rom stage.val tool.val) := raw.2
  have rawFrame := stage_control_frame q full CB P before rawRead
    (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) rawHeap
  have rawInput : ScanInput q full CB P rawRead := ScanInput.of_stageFrame ready.input layout rawFrame raw.1
  have rawPC : rawRead.pc = 5 * (start + 77) := by
    rw [runOps_pc rom _ tested (by simp [stageRead, loadRel, storeRel, NoJump]), testPC, show stageRead.length = 17 from rfl]
    omega
  have rawActive : rawRead.halted = false := (runOps_halted rom _ tested).trans testActive
  have rawRun : natRun rom containing 17 tested = rawRead :=
    stage_chunk_run rom containing start code .read tested testPC testActive
  have rawNumeric := stageRead_numeric q full B H CB stage tool tested testRegs
    ready.input.address ready.stage_cell ready.tool_cell ready.input.tools
    (actual_stage_input_end_le_wordLimit q full) room.1 hH
  have rawSafe := stage_chunk_safe_at rom B H containing start code .read tested
    testPC testActive rawNumeric 77 (by decide) rawPC
  change RunFacts B H rom containing 17 tested at rawSafe
  have rawRegs : RegistersLE B rawRead := by
    have h := ((rawSafe.1).final _ _ _ _ _).1
    rw [rawRun] at h
    exact h
  have rawNode : rawRead.heap (CB + 19) = node.val := by
    rw [rawHeap, Function.update_of_ne (by omega)]
    exact ready.node_cell
  have rawTool : rawRead.heap (CB + 20) = tool.val := by
    rw [rawHeap, Function.update_of_ne (by omega)]
    exact ready.tool_cell
  let arguments := runOps rom scanArguments rawRead
  have args := scanArguments_effect rom CB node.val tool.val rawRead raw.1 rawNode rawTool
  have argumentsHeap : arguments.heap = rawRead.heap := args.2.2.2
  have argumentsRaw : RawCardData q full CB arguments :=
    RawCardData.of_children_frame rawInput.raw (fun address _ => congrFun argumentsHeap address)
  have argsPC : arguments.pc = 5 * (start + 83) := by
    rw [runOps_pc rom _ rawRead (by simp [scanArguments, loadRel, NoJump]), rawPC, show scanArguments.length = 6 from rfl]
    omega
  have argsActive : arguments.halted = false := (runOps_halted rom _ rawRead).trans rawActive
  have argsRun : natRun rom containing 6 rawRead = arguments :=
    stage_chunk_run rom containing start code .arguments rawRead rawPC rawActive
  have argsNumeric := scanArguments_numeric rom B H CB M node.val tool.val rawRead rawRegs raw.1
    rawNode rawTool (by omega) (by omega) room.1 hH
  have argsSafe := stage_chunk_safe_at rom B H containing start code .arguments rawRead
    rawPC rawActive argsNumeric 83 (by decide) argsPC
  change RunFacts B H rom containing 6 rawRead at argsSafe
  have argsRegs : RegistersFit bits arguments := by
    intro reg
    have h := (((argsSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
    rw [argsRun] at h
    exact h
  let readClock := nodeReadClock full.length arguments.heap CB M node.val tool.val
  let read := natRun rom containing readClock arguments
  have queryEnd : Fits bits (5 * (start + 83 + 46)) :=
    (show 5 * (start + 83 + 46) ≤ 5 * containing.length by have hb := code.1; omega).trans_lt hcodePC
  have exactQuery := nodeBit_actual_exact_runFacts q full hq containing (start + 83)
    (stage_query_code containing start code) arguments argumentsRaw node tool argsPC argsActive
    args.1 args.2.1 args.2.2.1 argsRegs queryEnd
  have readSafe : RunFacts B H rom containing readClock arguments := exactQuery.2
  have readRegs : RegistersLE B read := ((readSafe.1).final _ _ _ _ _).1
  have result := nodeBit_nat_read q full containing (start + 83) (stage_query_code containing start code)
    CB arguments argumentsRaw node tool argsPC argsActive args.1 args.2.1 args.2.2.1
  change read.register .value = rawCandidateBit rom
    (arguments.heap (rawOrdAddress CB M node.val)) tool.val ∧
    read.register .fresh = tool.val ∧ read.register .address = CB ∧ read.heap = arguments.heap ∧
    read.pc = 5 * (start + 129) ∧ read.halted = false at result
  have readHeap : read.heap = Function.update before.heap (CB + 24) (rawStageBit rom stage.val tool.val) :=
    result.2.2.2.1.trans (argumentsHeap.trans rawHeap)
  have readValue : read.register .value = rawCandidateBit rom
      (reference.heap (rawOrdAddress CB M node.val)) tool.val := by
    rw [result.1]
    exact (rawNodeBit_eq_decode q full CB arguments argumentsRaw node tool).trans
      (rawNodeBit_eq_decode q full CB reference referenceData node tool).symm
  have readMatch : read.heap (CB + 23) = bit (stageMatchTools rom reference.heap CB M stage.val node.val tool.val) := by
    rw [readHeap, Function.update_of_ne (by omega)]
    exact ready.match_cell
  have readStage : read.heap (CB + 24) = rawStageBit rom stage.val tool.val := by
    rw [readHeap, Function.update_self]
  have readMatchBound : read.heap (CB + 23) ≤ 1 := by
    rw [readMatch]
    cases stageMatchTools rom reference.heap CB M stage.val node.val tool.val <;> decide
  have readStageBound : read.heap (CB + 24) ≤ 1 := by
    rw [readStage]
    exact rawStageBit_le_one q full stage tool
  have readValueBound : read.register .value ≤ 1 := by
    rw [result.1]
    exact raw_node_bit_le_one q full CB arguments argumentsRaw node tool
  let compared := runOps rom stageCompare read
  have compare := stageCompare_effect rom CB _ _ read result.2.2.1 readMatch readStage
  have compareHeap : compared.heap = Function.update
      (Function.update before.heap (CB + 24) (rawStageBit rom stage.val tool.val)) (CB + 23)
      (bit (stageMatchTools rom reference.heap CB M stage.val node.val (tool.val + 1))) := by
    rw [compare.2, readHeap, readValue, bit_and_comparison]
    rfl
  have comparePC : compared.pc = 5 * (start + 143) := by
    rw [runOps_pc rom _ read (by simp [stageCompare, loadRel, storeRel, NoJump]), result.2.2.2.2.1, show stageCompare.length = 14 from rfl]
    omega
  have compareActive : compared.halted = false := (runOps_halted rom _ read).trans result.2.2.2.2.2
  have compareRun : natRun rom containing 14 read = compared :=
    stage_chunk_run rom containing start code .compare read result.2.2.2.2.1 result.2.2.2.2.2
  have compareNumeric := stageCompare_numeric rom B H CB M read readRegs result.2.2.1
    readMatchBound readStageBound readValueBound room.1 hH
  have compareSafe := stage_chunk_safe_at rom B H containing start code .compare read
    result.2.2.2.2.1 result.2.2.2.2.2 compareNumeric 143 (by decide) comparePC
  change RunFacts B H rom containing 14 read at compareSafe
  have compareRegs : RegistersLE B compared := by
    have h := ((compareSafe.1).final _ _ _ _ _).1
    rw [compareRun] at h
    exact h
  have compareTool : compared.heap (CB + 20) = tool.val := by
    rw [compareHeap, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact ready.tool_cell
  let after := runOps rom (stageToolTail start) compared
  have tail := scanInnerTail_effect rom CB tool.val start compared compare.1 compareTool
  have afterHeap : after.heap = stageToolHeap q full reference CB stage.val node.val tool.val before.heap := by
    change (runOps rom (scanInnerTail start) compared).heap = _
    rw [tail.2.1, compareHeap]
    rfl
  have next := stage_tool_heap_ready q full CB P reference stage node tool (5 * (start + 51)) before after
    ready layout afterHeap tail.1 tail.2.2.1 ((tail.2.2.2).trans compareActive)
  have tailRun : natRun rom containing 11 compared = after :=
    stage_chunk_run rom containing start code .toolTail compared comparePC compareActive
  have tailNumeric := scanInnerTail_numeric rom B H CB M tool.val start compared compareRegs compare.1
    compareTool (by omega) (jump 51 (by decide)) room.1 hH
  have tailSafe := stage_chunk_safe_at rom B H containing start code .toolTail compared
    comparePC compareActive tailNumeric 51 (by decide) tail.2.2.1
  change RunFacts B H rom containing 11 compared at tailSafe
  have readHeadSafe := RunFacts.add B H rom containing 9 17 before testSafe
    (by rw [testRun]; exact rawSafe)
  have readHeadRun : natRun rom containing (9 + 17) before = rawRead := by
    rw [natRun_add rom containing 9 17 before, testRun, rawRun]
  have argsHeadSafe := RunFacts.add B H rom containing (9 + 17) 6 before readHeadSafe
    (by rw [readHeadRun]; exact argsSafe)
  have argsHeadRun : natRun rom containing (9 + 17 + 6) before = arguments := by
    rw [natRun_add rom containing (9 + 17) 6 before, readHeadRun, argsRun]
  have queryHeadSafe := RunFacts.add B H rom containing (9 + 17 + 6) readClock before argsHeadSafe
    (by rw [argsHeadRun]; exact readSafe)
  have queryHeadRun : natRun rom containing (9 + 17 + 6 + readClock) before = read := by
    rw [natRun_add rom containing (9 + 17 + 6) readClock before, argsHeadRun]
  have compareHeadSafe := RunFacts.add B H rom containing (9 + 17 + 6 + readClock) 14 before queryHeadSafe
    (by rw [queryHeadRun]; exact compareSafe)
  have compareHeadRun : natRun rom containing (9 + 17 + 6 + readClock + 14) before = compared := by
    rw [natRun_add rom containing (9 + 17 + 6 + readClock) 14 before, queryHeadRun, compareRun]
  have allSafe := RunFacts.add B H rom containing (9 + 17 + 6 + readClock + 14) 11 before compareHeadSafe
    (by rw [compareHeadRun]; exact tailSafe)
  have actual : natRun rom containing (9 + 17 + 6 + readClock + 14 + 11) before = after := by
    rw [natRun_add rom containing (9 + 17 + 6 + readClock + 14) 11 before, compareHeadRun, tailRun]
  refine ⟨9 + 17 + 6 + readClock + 14 + 11, ?_, rfl, ?_⟩
  · have hc := nodeReadClock_le full.length arguments.heap CB M node.val tool.val
    change readClock ≤ 33 at hc
    omega
  · rw [actual]
    exact ⟨next.1, next.2, allSafe⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
