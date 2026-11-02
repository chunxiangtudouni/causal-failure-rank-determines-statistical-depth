module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordScanInitialize
public import Structure.PA06_A19Prepare_StaticMetadata036_WordQueryExact

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED one-pair all-clock safety of the actual191-op scanner.
The query clock is precisely nodeReadClock<=33. Inputs are the actual raw
cache, permanent cells and current loop controls; no whole-run safety,
future leaf/tool table or arbitrary-heap bound is a premise. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass highCacheEnd actualPackedWords actualControlBase actualAllocation RunFacts)

def scanPairClock (q : Nat) (full : List (Finset (Fin q))) (CB : Nat) (state : NatState) (node tool : Nat) : Nat :=
  (9 + 6 + nodeReadClock full.length state.heap CB (mass q full) node tool + 11) +
    (if scanMatch (rawIncidenceROM q full) state.heap CB (mass q full) node tool then 46 else 0) + 11

theorem scanPairClock_le (q : Nat) (full : List (Finset (Fin q))) (CB : Nat)
    (state : NatState) (node tool : Nat) : scanPairClock q full CB state node tool ≤ 116 := by
  have h := nodeReadClock_le full.length state.heap CB (mass q full) node tool
  unfold scanPairClock
  split_ifs <;> omega

/-- This is exactly the constructive clock in existing ScanIteration:
argument loads do not change the heap, and the reference match is stable
under real RawCardData. No equality of future states is assumed. -/
theorem scanPairClock_nat_iteration (q : Nat) (full : List (Finset (Fin q))) (CB start : Nat)
    (reference before : NatState) (referenceData : RawCardData q full CB reference)
    (inputData : RawCardData q full CB before)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q) :
    let tested := runOps (rawIncidenceROM q full) (scanBoundedTest 1 20 (start + 180)) before
    let arguments := runOps (rawIncidenceROM q full) scanArguments tested
    scanPairClock q full CB before node.val tool.val =
      (9 + 6 + nodeReadClock full.length arguments.heap CB (mass q full) node.val tool.val + 11) +
        (if scanMatch (rawIncidenceROM q full) reference.heap CB (mass q full) node.val tool.val then 46 else 0) + 11 := by
  have stable := scanMatch_stable q full CB reference before referenceData inputData node tool
  change scanPairClock q full CB before node.val tool.val =
    (9 + 6 + nodeReadClock full.length before.heap CB (mass q full) node.val tool.val + 11) +
      (if scanMatch (rawIncidenceROM q full) reference.heap CB (mass q full) node.val tool.val then 46 else 0) + 11
  rw [stable]
  rfl

theorem scan_pair_actual_runFacts (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start)
    (before : NatState)
    (input : ScanInput q full (actualControlBase q full) (actualPackedWords q full) before)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (hnode : before.heap (actualControlBase q full + 19) = node.val)
    (htool : before.heap (actualControlBase q full + 20) = tool.val)
    (hcard : before.heap (actualControlBase q full + 21) =
      (prepareNormalization q full).indexed.metadata.cardinalities.get node)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hpc : before.pc = 5 * (start + 51)) (ha : before.halted = false)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
      (rawIncidenceROM q full) containing
      (scanPairClock q full (actualControlBase q full) before node.val tool.val) before := by
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
  have hj := tool.isLt
  have qM : q ≤ M := by dsimp only [M, mass]; omega
  have cardBound : (prepareNormalization q full).indexed.metadata.cardinalities.get node ≤ M :=
    (metadata_cardinality_le_q q (prepareNormalization q full).indexed node).trans qM
  have jump (offset : Nat) (ho : offset ≤ 191) : 5 * (start + offset) ≤ B := by
    have hb := code.1
    have hc : 5 * containing.length ≤ B := metadata_le_wordLimit hcodePC
    omega
  let tested := runOps rom (scanBoundedTest 1 20 (start + 180)) before
  have testNumeric := scanBoundedTest_numeric rom B H CB M q tool.val 1 20 (start + 180) before
    regs input.address input.tools htool (by decide) (by decide) qM (by omega)
    (jump 180 (by decide)) room.1 hH
  have testSafe := scan_chunk_safe rom B H containing start code .innerTest before hpc ha testNumeric
  change RunFacts B H rom containing 9 before at testSafe
  have testRun : natRun rom containing 9 before = tested :=
    scan_chunk_run rom containing start code .innerTest before hpc ha
  have testRegs : RegistersLE B tested := by
    have h := ((testSafe.1).final _ _ _ _ _).1
    rw [testRun] at h
    exact h
  have testPC : tested.pc = 5 * (start + 60) := by
    rw [scanBoundedTest_pc rom CB q tool.val 1 20 (start + 180) before input.address input.tools htool,
      ite_eq_right (by omega), hpc]
    omega
  have testActive : tested.halted = false := (runOps_halted rom _ before).trans ha
  have testedHeap : tested.heap = before.heap := rfl
  let arguments := runOps rom scanArguments tested
  have args := scanArguments_effect rom CB node.val tool.val tested input.address hnode htool
  have argumentsHeap : arguments.heap = before.heap := args.2.2.2.trans testedHeap
  have argumentsRaw : RawCardData q full CB arguments :=
    RawCardData.of_children_frame input.raw (fun address _ => congrFun argumentsHeap address)
  have argsNumeric := scanArguments_numeric rom B H CB M node.val tool.val tested testRegs input.address
    hnode htool (by omega) (by omega) room.1 hH
  have argsSafe := scan_chunk_safe rom B H containing start code .arguments tested testPC testActive argsNumeric
  change RunFacts B H rom containing 6 tested at argsSafe
  have argsRun : natRun rom containing 6 tested = arguments :=
    scan_chunk_run rom containing start code .arguments tested testPC testActive
  have argsRegs : RegistersLE B arguments := by
    have h := ((argsSafe.1).final _ _ _ _ _).1
    rw [argsRun] at h
    exact h
  have argsPC : arguments.pc = 5 * (start + 66) := by
    rw [runOps_pc rom _ tested (by simp [scanArguments, PA06A19PrepareChildrenCache023.loadRel, NoJump]), testPC, show scanArguments.length = 6 from rfl]
    omega
  have argsActive : arguments.halted = false := (runOps_halted rom _ tested).trans testActive
  let readClock := nodeReadClock full.length before.heap CB M node.val tool.val
  let read := natRun rom containing readClock arguments
  have queryEnd : Fits bits (5 * (start + 66 + 46)) :=
    (show 5 * (start + 66 + 46) ≤ 5 * containing.length by have hb := code.1; omega).trans_lt hcodePC
  have exactQuery := nodeBit_actual_exact_runFacts q full hq containing (start + 66)
    (scan_query_code containing start code) arguments argumentsRaw node tool argsPC argsActive
    args.1 args.2.1 args.2.2.1 (fun reg => (argsRegs reg).trans_lt (metadata_wordLimit_fits bits)) queryEnd
  have readSafe : RunFacts B H rom containing readClock arguments := exactQuery.2
  have readRegs : RegistersLE B read := ((readSafe.1).final _ _ _ _ _).1
  have result := nodeBit_nat_read q full containing (start + 66) (scan_query_code containing start code)
    CB arguments argumentsRaw node tool argsPC argsActive args.1 args.2.1 args.2.2.1
  change read.register .value = rawCandidateBit rom
    (before.heap (rawOrdAddress CB M node.val)) tool.val ∧
    read.register .fresh = tool.val ∧ read.register .address = CB ∧ read.heap = before.heap ∧
    read.pc = 5 * (start + 112) ∧ read.halted = false at result
  have readCard : read.heap (CB + 21) = (prepareNormalization q full).indexed.metadata.cardinalities.get node := by
    rw [result.2.2.2.1]
    exact hcard
  let scored := runOps rom (scanScore (start + 169)) read
  let matched := scanMatch rom before.heap CB M node.val tool.val
  have gate : ((prepareNormalization q full).indexed.metadata.cardinalities.get node = 1 ∧
      read.register .value ≠ 0) ↔ matched = true := by
    rw [result.1]
    have hb : rawCandidateBit rom (before.heap (rawOrdAddress CB M node.val)) tool.val ≤ 1 :=
      raw_node_bit_le_one q full CB before input.raw node tool
    dsimp only [matched, M] at hb ⊢
    simp only [scanMatch, Bool.and_eq_true, decide_eq_true_eq,
      rawCardData_node_card q full CB before input.raw node]
    omega
  have scorePC : scored.pc = if matched then 5 * (start + 123) else 5 * (start + 169) := by
    rw [scanScore_pc rom CB _ (start + 169) read result.2.2.1 readCard, result.2.2.2.2.1]
    by_cases hm : matched = true
    · have condition := gate.mpr hm
      rw [ite_eq_left condition]
      simp only [hm, ite_true]
      omega
    · have condition : ¬ ((prepareNormalization q full).indexed.metadata.cardinalities.get node = 1 ∧
          read.register .value ≠ 0) := fun h => hm (gate.mp h)
      have hf : matched = false := by cases h : matched <;> simp_all
      rw [ite_eq_right condition]
      simp only [hf, Bool.false_eq_true, ite_false]
  have scoreActive : scored.halted = false := (runOps_halted rom _ read).trans result.2.2.2.2.2
  have scoreCB : scored.register .address = CB := result.2.2.1
  have scoreHeap : scored.heap = before.heap := result.2.2.2.1
  have scoreNumeric := scanScore_numeric rom B H CB M
    ((prepareNormalization q full).indexed.metadata.cardinalities.get node) (start + 169) read
    readRegs result.2.2.1 readCard cardBound (jump 169 (by decide)) room.1 hH
  have scoreSafe := scan_chunk_safe rom B H containing start code .score read
    result.2.2.2.2.1 result.2.2.2.2.2 scoreNumeric
  change RunFacts B H rom containing 11 read at scoreSafe
  have scoreRun : natRun rom containing 11 read = scored :=
    scan_chunk_run rom containing start code .score read result.2.2.2.2.1 result.2.2.2.2.2
  have scoreRegs : RegistersLE B scored := by
    have h := ((scoreSafe.1).final _ _ _ _ _).1
    rw [scoreRun] at h
    exact h
  have firstSafe := RunFacts.add B H rom containing 9 6 before testSafe (by rw [testRun]; exact argsSafe)
  have firstRun : natRun rom containing (9 + 6) before = arguments := by
    rw [natRun_add rom containing 9 6 before, testRun, argsRun]
  have queriedSafe := RunFacts.add B H rom containing (9 + 6) readClock before firstSafe (by rw [firstRun]; exact readSafe)
  have queriedRun : natRun rom containing (9 + 6 + readClock) before = read := by
    rw [natRun_add rom containing (9 + 6) readClock before, firstRun]
  have headSafe := RunFacts.add B H rom containing (9 + 6 + readClock) 11 before queriedSafe
    (by rw [queriedRun]; exact scoreSafe)
  have headRun : natRun rom containing (9 + 6 + readClock + 11) before = scored := by
    rw [natRun_add rom containing (9 + 6 + readClock) 11 before, queriedRun, scoreRun]
  have scoreTool : scored.heap (CB + 20) = tool.val := by rw [scoreHeap]; exact htool
  have toolBound : tool.val + 1 ≤ M := by omega
  change RunFacts B H rom containing
    ((9 + 6 + readClock + 11) + (if matched then 46 else 0) + 11) before
  by_cases hm : matched = true
  · have matchedPC : scored.pc = 5 * (start + 123) := by simp only [scorePC, hm, ite_true]
    have numeric := recordSingleton_numeric rom B H CB P full.length q (preparedSize q full) node.val tool.val scored
      scoreRegs scoreCB (by rw [scoreHeap]; exact input.base) (by rw [scoreHeap]; exact input.nodes)
      (by rw [scoreHeap]; exact input.stages) (by rw [scoreHeap]; exact hnode) scoreTool
      node.isLt tool.isLt htM rfl room.1 hH
    have matchSafe := scan_chunk_safe rom B H containing start code .matched scored matchedPC scoreActive numeric
    change RunFacts B H rom containing 46 scored at matchSafe
    let stored := runOps rom recordSingleton scored
    have matchRun : natRun rom containing 46 scored = stored :=
      scan_chunk_run rom containing start code .matched scored matchedPC scoreActive
    have storedRegs : RegistersLE B stored := by
      have h := ((matchSafe.1).final _ _ _ _ _).1
      rw [matchRun] at h
      exact h
    have effect := recordSingleton_effect rom CB P full.length q (preparedSize q full) node.val tool.val scored
      scoreCB (by rw [scoreHeap]; exact input.base) (by rw [scoreHeap]; exact input.nodes)
      (by rw [scoreHeap]; exact input.stages) (by rw [scoreHeap]; exact hnode) scoreTool node.isLt tool.isLt rfl
    have leafBelow : fieldAddress P full.length (preparedSize q full) .leaf node.val < CB :=
      fieldAddress_lt_control full.length q (preparedSize q full) P .leaf node.val node.isLt
    have toolBelow : fieldAddress P full.length (preparedSize q full) .tool tool.val < CB :=
      fieldAddress_lt_control full.length q (preparedSize q full) P .tool tool.val tool.isLt
    have storedTool : stored.heap (CB + 20) = tool.val := by
      rw [effect.2]
      simp (disch := omega) [scoreTool]
    have storedPC : stored.pc = 5 * (start + 169) := by
      rw [runOps_pc rom _ scored recordSingleton_noJump, matchedPC, recordSingleton_length]
      omega
    have storedActive : stored.halted = false := (runOps_halted rom _ scored).trans scoreActive
    have tailNumeric := scanInnerTail_numeric rom B H CB M tool.val start stored
      storedRegs effect.1 storedTool toolBound (jump 51 (by decide)) room.1 hH
    have tailSafe := scan_chunk_safe rom B H containing start code .innerTail stored storedPC storedActive tailNumeric
    change RunFacts B H rom containing 11 stored at tailSafe
    have headMatch := RunFacts.add B H rom containing (9 + 6 + readClock + 11) 46 before headSafe
      (by rw [headRun]; exact matchSafe)
    have headMatchRun : natRun rom containing (9 + 6 + readClock + 11 + 46) before = stored := by
      rw [natRun_add rom containing (9 + 6 + readClock + 11) 46 before, headRun, matchRun]
    have all := RunFacts.add B H rom containing (9 + 6 + readClock + 11 + 46) 11 before headMatch
      (by rw [headMatchRun]; exact tailSafe)
    simpa only [hm, ite_true] using all
  · have hf : matched = false := by cases h : matched <;> simp_all
    have tailPC : scored.pc = 5 * (start + 169) := by simp only [scorePC, hf, Bool.false_eq_true, ite_false]
    have tailNumeric := scanInnerTail_numeric rom B H CB M tool.val start scored
      scoreRegs scoreCB scoreTool toolBound (jump 51 (by decide)) room.1 hH
    have tailSafe := scan_chunk_safe rom B H containing start code .innerTail scored tailPC scoreActive tailNumeric
    change RunFacts B H rom containing 11 scored at tailSafe
    have all := RunFacts.add B H rom containing (9 + 6 + readClock + 11) 11 before headSafe
      (by rw [headRun]; exact tailSafe)
    simpa only [hf, Bool.false_eq_true, ite_false, Nat.add_zero] using all

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
