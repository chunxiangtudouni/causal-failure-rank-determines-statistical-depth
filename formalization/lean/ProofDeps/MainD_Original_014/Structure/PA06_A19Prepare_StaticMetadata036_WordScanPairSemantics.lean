module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordScanPair

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED named-clock semantic pair plus the existing actual RunFacts.
Only the short assembly choice of ScanIteration is restated: the real query,
block effects and pair_heap_ready are reused. No opaque existential clock
is identified with a named clock and no query/numeric path is reproved.
This file does not aggregate the inner/outer loops or the202 stage scan. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass actualPackedWords actualControlBase actualAllocation RunFacts)

private theorem raw_bit_gate_local (card value : Nat) (bound : value ≤ 1) :
    (card = 1 ∧ value ≠ 0) ↔ (card = 1 ∧ value = 1) := by omega

section Actual
variable (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
  (reference : NatState) (referenceData : RawCardData q full CB reference)
  (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
  (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start)

include referenceData hlayout code

/-- Existing semantic invariant/frame update at exactly scanPairClock.
Incoming ready describes only the current real loop state and past writes;
future leaf/tool values and an all-run safety premise are not inputs. -/
theorem scan_pair_named_semantics (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (before : NatState)
    (ready : LeafInnerReady q full CB P reference node tool.val (5 * (start + 51)) before) :
    let clock := scanPairClock q full CB before node.val tool.val
    let after := natRun (rawIncidenceROM q full) containing clock before
    LeafInnerReady q full CB P reference node (tool.val + 1) (5 * (start + 51)) after ∧
      ScanFrame q full CB P before after := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (scanBoundedTest 1 20 (start + 180)) before
  have htpc : tested.pc = 5 * (start + 60) := by
    rw [scanBoundedTest_pc rom CB q tool.val 1 20 (start + 180) before
      ready.input.address ready.input.tools ready.tool_cell, ite_eq_right (by have h := tool.isLt; omega), ready.pc]
    omega
  have hta : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  have htRun : natRun rom containing 9 before = tested := by
    exact scan_chunk_run rom containing start code .innerTest before ready.pc ready.active
  have testedHeap : tested.heap = before.heap := rfl
  let arguments := runOps rom scanArguments tested
  have args := scanArguments_effect rom CB node.val tool.val tested
    ready.input.address ready.node_cell ready.tool_cell
  have argumentsHeap : arguments.heap = before.heap := args.2.2.2.trans testedHeap
  have argumentsRaw : RawCardData q full CB arguments :=
    RawCardData.of_children_frame ready.input.raw (fun address _ => congrFun argumentsHeap address)
  have haPC : arguments.pc = 5 * (start + 66) := by
    rw [runOps_pc rom _ tested (by simp [scanArguments, PA06A19PrepareChildrenCache023.loadRel, NoJump]), htpc, show scanArguments.length = 6 from rfl]
    omega
  have haActive : arguments.halted = false := (runOps_halted rom _ tested).trans hta
  have haRun : natRun rom containing 6 tested = arguments :=
    scan_chunk_run rom containing start code .arguments tested htpc hta
  let readClock := nodeReadClock full.length arguments.heap CB (mass q full) node.val tool.val
  let read := natRun rom containing readClock arguments
  have result := nodeBit_nat_read q full containing (start + 66) (scan_query_code containing start code)
    CB arguments argumentsRaw node tool haPC haActive args.1 args.2.1 args.2.2.1
  change read.register .value = rawCandidateBit rom
    (arguments.heap (rawOrdAddress CB (mass q full) node.val)) tool.val ∧
    read.register .fresh = tool.val ∧ read.register .address = CB ∧ read.heap = arguments.heap ∧
    read.pc = 5 * (start + 112) ∧ read.halted = false at result
  rw [argumentsHeap] at result
  have readHeap : read.heap = before.heap := result.2.2.2.1
  have readCard : read.heap (CB + 21) = (prepareNormalization q full).indexed.metadata.cardinalities.get node := by
    rw [readHeap]
    exact ready.card_cell
  let scored := runOps rom (scanScore (start + 169)) read
  let matched := scanMatch rom reference.heap CB (mass q full) node.val tool.val
  have stable := scanMatch_stable q full CB reference before referenceData ready.input.raw node tool
  have gate : ((prepareNormalization q full).indexed.metadata.cardinalities.get node = 1 ∧ read.register .value ≠ 0) ↔ matched = true := by
    rw [result.1]
    have hb : rawCandidateBit rom (before.heap (rawOrdAddress CB (mass q full) node.val)) tool.val ≤ 1 :=
      raw_node_bit_le_one q full CB before ready.input.raw node tool
    dsimp only [matched]
    rw [stable]
    simp only [scanMatch, Bool.and_eq_true, decide_eq_true_eq,
      rawCardData_node_card q full CB before ready.input.raw node]
    exact raw_bit_gate_local _ _ hb
  have hsPC : scored.pc = if matched then 5 * (start + 123) else 5 * (start + 169) := by
    rw [scanScore_pc rom CB _ (start + 169) read result.2.2.1 readCard, result.2.2.2.2.1]
    by_cases hm : matched = true
    · have condition := gate.mpr hm
      rw [ite_eq_left condition, ite_eq_left hm]
      omega
    · have condition : ¬ ((prepareNormalization q full).indexed.metadata.cardinalities.get node = 1 ∧
          read.register .value ≠ 0) := fun h => hm (gate.mp h)
      rw [ite_eq_right condition, ite_eq_right hm]
  have hsActive : scored.halted = false := (runOps_halted rom _ read).trans result.2.2.2.2.2
  have hsCB : scored.register .address = CB := result.2.2.1
  have hsHeap : scored.heap = before.heap := readHeap
  have hsRun : natRun rom containing 11 read = scored :=
    scan_chunk_run rom containing start code .score read result.2.2.2.2.1 result.2.2.2.2.2
  let stored := if matched then runOps rom recordSingleton scored else scored
  have layout : CB = 4 + P + 4096 * (full.length + q + 1 + preparedSize q full) := hlayout
  have hn : node.val < preparedSize q full := node.isLt
  have hj := tool.isLt
  have hleaf : fieldAddress P full.length (preparedSize q full) .leaf node.val < CB := by
    change 6 + P + 5 * preparedSize q full + node.val < CB
    omega
  have htool : fieldAddress P full.length (preparedSize q full) .tool tool.val < CB := by
    change 6 + P + 6 * preparedSize q full + full.length + tool.val < CB
    omega
  have storedHeap : stored.heap = if matched then
      Function.update (Function.update before.heap (fieldAddress P full.length (preparedSize q full) .leaf node.val) (tool.val + 1))
        (fieldAddress P full.length (preparedSize q full) .tool tool.val) (node.val + 1) else before.heap := by
    by_cases hm : matched = true
    · simp only [stored, hm, ite_true]
      have h := recordSingleton_effect rom CB P full.length q (preparedSize q full) node.val tool.val scored
        hsCB (by rw [hsHeap]; exact ready.input.base) (by rw [hsHeap]; exact ready.input.nodes)
        (by rw [hsHeap]; exact ready.input.stages) (by rw [hsHeap]; exact ready.node_cell)
        (by rw [hsHeap]; exact ready.tool_cell) node.isLt tool.isLt hlayout
      simpa only [hsHeap] using h.2
    · have hf : matched = false := by cases hm' : matched <;> simp_all
      simp only [stored, hf, Bool.false_eq_true, ite_false, hsHeap]
  have storedCB : stored.register .address = CB := by
    by_cases hm : matched = true <;> simp only [stored, hm, ite_true, Bool.false_eq_true, ite_false]
    · exact hsCB
    · exact hsCB
  have storedPC : stored.pc = 5 * (start + 169) := by
    by_cases hm : matched = true
    · simp only [stored, hm, ite_true]
      rw [runOps_pc rom _ scored recordSingleton_noJump, hsPC, ite_eq_left hm, recordSingleton_length]
      omega
    · have hf : matched = false := by cases hm' : matched <;> simp_all
      simp only [stored, hf, Bool.false_eq_true, ite_false, hsPC]
  have storedActive : stored.halted = false := by
    by_cases hm : matched = true
    · simpa only [stored, hm, ite_true] using (runOps_halted rom recordSingleton scored).trans hsActive
    · have hf : matched = false := by cases hm' : matched <;> simp_all
      simpa only [stored, hf, Bool.false_eq_true, ite_false] using hsActive
  have storedTool : stored.heap (CB + 20) = tool.val := by
    rw [storedHeap]
    split_ifs <;> simp (disch := omega) [ready.tool_cell]
  let after := runOps rom (scanInnerTail start) stored
  have tail := scanInnerTail_effect rom CB tool.val start stored storedCB storedTool
  have hpair : after.heap = pairHeap q full reference CB P node.val tool.val before.heap := by
    rw [tail.2.1, storedHeap]
    rfl
  have hready := pair_heap_ready q full CB P reference referenceData node tool (5 * (start + 51))
    before after ready hlayout hpair tail.1 tail.2.2.1 ((tail.2.2.2).trans storedActive)
  have hHead : natRun rom containing (9 + 6 + readClock + 11) before = scored := by
    rw [natRun_add rom containing (9 + 6 + readClock) 11 before,
      natRun_add rom containing (9 + 6) readClock before,
      natRun_add rom containing 9 6 before, htRun, haRun, hsRun]
  have hStore : natRun rom containing (if matched then 46 else 0) scored = stored := by
    by_cases hm : matched = true
    · simp only [stored, hm, ite_true]
      exact scan_chunk_run rom containing start code .matched scored
        (by simp only [scanChunkOffset, hsPC, hm, ite_true]) hsActive
    · have hf : matched = false := by cases hm' : matched <;> simp_all
      simp only [stored, hf, Bool.false_eq_true, ite_false, natRun]
  have hTail : natRun rom containing 11 stored = after :=
    scan_chunk_run rom containing start code .innerTail stored storedPC storedActive
  have actualClock : scanPairClock q full CB before node.val tool.val =
      (9 + 6 + readClock + 11) + (if matched then 46 else 0) + 11 := by
    exact scanPairClock_nat_iteration q full CB start reference before referenceData ready.input.raw node tool
  dsimp only
  rw [actualClock,
    natRun_add rom containing ((9 + 6 + readClock + 11) + (if matched then 46 else 0)) 11 before,
    natRun_add rom containing (9 + 6 + readClock + 11) (if matched then 46 else 0) before,
    hHead, hStore, hTail]
  exact hready

end Actual

/-- One actual witness carries the exact named clock, semantic next-state
invariant, ordinary heap frame AND every real prefix register/PC/access/CB
bound on the original common32/8192 allocation. No full loop is claimed. -/
theorem scan_pair_named_witness (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (referenceData : RawCardData q full (actualControlBase q full) reference)
    (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q) (before : NatState)
    (ready : LeafInnerReady q full (actualControlBase q full) (actualPackedWords q full)
      reference node tool.val (5 * (start + 51)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    ∃ clock ≤ 116, clock = scanPairClock q full (actualControlBase q full) before node.val tool.val ∧
      let after := natRun (rawIncidenceROM q full) containing clock before
      LeafInnerReady q full (actualControlBase q full) (actualPackedWords q full)
        reference node (tool.val + 1) (5 * (start + 51)) after ∧
      ScanFrame q full (actualControlBase q full) (actualPackedWords q full) before after ∧
      RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
        (rawIncidenceROM q full) containing clock before := by
  have semantic := scan_pair_named_semantics q full (actualControlBase q full) (actualPackedWords q full)
    reference referenceData rfl containing start code node tool before ready
  have safe := scan_pair_actual_runFacts q full hq containing start code before ready.input node tool
    ready.node_cell ready.tool_cell ready.card_cell hr ready.pc ready.active hcodePC
  exact ⟨scanPairClock q full (actualControlBase q full) before node.val tool.val,
    scanPairClock_le q full (actualControlBase q full) before node.val tool.val,
    rfl, semantic.1, semantic.2, safe⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
