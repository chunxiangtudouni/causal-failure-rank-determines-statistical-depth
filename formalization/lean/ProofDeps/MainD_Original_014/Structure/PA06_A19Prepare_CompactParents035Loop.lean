module

public import Structure.PA06_A19Prepare_CompactParents035Data
public import Structure.PA06_A19Prepare_ROM_001

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! The unchanged361-op dynamic parent search, with actual B16/fullwidth32
prefix safety assembled from035 source-qualified pieces and the frozen125
PairScan. Nat parent/search semantics are reused. The physical controller
input is the true raw ROM with appended initialUsed bits, transported only
through proved accesses. No hSafe, Fit16 or parent answer is a premise. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Loop

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateParentRAM RawIncidenceScanSafety
open RawCandidateOrderingRAM (arraySlot testWorkspace testWorkspace_effect)
open RawCandidateWorkspaceInit (candidateCount)
open RawCandidateParentWordChunks (Chunk chunkCode chunkOffset chunkLength)
open PA06A19PrepareCompactParents035Safety (SafePoint)
open PA06A19PrepareCompactParents035Data

abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 361 ≤ containing.length)
  (hcode : ∀ position < 361, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode
theorem inner_iteration_safe (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (16) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (node later : Nat) (hn : node < nodes)
    (hj : later < candidateCount full.length q)
    (hnode : state.heap (16 + 1) = node)
    (hlater : state.heap (16 + 2) = later)
    (hbest : state.heap (16 + 3) ≤ q + 1)
    (hparent : Fits (indexWidth 32 full.length q)
      (state.heap (parentSlot (16) (candidateCount full.length q) node)))
    (hpc : state.pc = 5 * (start + 64)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (innerIterationSteps full.length q (order node) later) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (innerIterationSteps full.length q (order node) later) state) := by
  let rom := rawIncidenceROM q full
  let B := 16
  let M := candidateCount full.length q
  have hb : 16 ≤ B := (show 16 ≤ 16 from le_rfl)
  have ht : nodes ≤ M := tables.nodes_le
  let tested := runOps rom (testWorkspace 2 (start + 346)) state
  have tv := testWorkspace_effect rom 2 (start + 346) state
  have th : tested.heap = state.heap := tv.1
  have tp : tested.pc = 5 * (start + 77) := by
    have hp := tv.2.1
    rw [tables.base_cell, tables.count_cell, hlater,
      ite_eq_right (Nat.sub_ne_zero_of_lt (show later < full.length + q + 1 from hj)), hpc] at hp
    change tested.pc = _ at hp
    omega
  have ta : tested.halted = false := tv.2.2.trans ha
  have tt := tables_of_heap_eq tables th
  have ss := chunk_of_macro q full containing start hbound hcode .innerTest state hpc ha
    (PA06A19PrepareCompactOrdering034Macros.testWorkspace_safe q full 2 (start + 346) (by omega) state hf tables.base_cell
      (by rw [tables.count_cell]; exact count_fits _ _)
      (by rw [hlater]; exact small_fits _ _ _ hj.le) (lt_of_le_of_lt (by omega) hend))
  rw [chunk_run q full containing start hbound hcode .innerTest state hpc ha] at ss
  let arguments := runOps rom pairArguments tested
  have ah : arguments.heap = Function.update (Function.update state.heap 1 (order node)) 2 later := by
    simpa only [th, tables.base_cell, tables.count_cell, hnode, hlater, tables.ordered node hn] using
      pairArguments_heap rom tested
  have aframe (address : Nat) (ha : 8 ≤ address) : arguments.heap address = state.heap address := by
    rw [ah, Function.update_of_ne (by omega : address ≠ 2), Function.update_of_ne (by omega : address ≠ 1)]
  have ap : arguments.pc = 5 * (start + 105) := by
    rw [show arguments = runOps rom pairArguments tested from rfl,
      runOps_pc rom pairArguments tested (by
        simp [pairArguments, RawCandidateOrderingRAM.loadArray, RawCandidateOrderingRAM.arrayAddress,
          RawCandidateOrderingRAM.arrayBase, RawCandidateOrderingRAM.loadWorkspace, loadCell, storeCell, NoJump]),
      pairArguments_length, tp]
    omega
  have aa : arguments.halted = false := (runOps_halted _ _ _).trans ta
  have asafe := chunk_of_macro q full containing start hbound hcode .pairArgs tested tp ta
    (PA06A19PrepareCompactParents035Pieces.pairArguments_safe q full tested ss.2 tt.base_cell tt.count_cell
      (by rw [th, hnode]; exact hn.le.trans ht) (by rw [th, hlater]; exact hj.le)
      (by rw [th, hnode]; exact order_word_fits tables node hn))
  rw [chunk_run q full containing start hbound hcode .pairArgs tested tp ta] at asafe
  let left : Fin (full.length + q + 1) := ⟨order node, tables.order_valid node hn⟩
  let right : Fin (full.length + q + 1) := ⟨later, hj⟩
  have ps := pair_safe_data q full containing start hbound hcode left right arguments ap aa
    (by rw [ah]; simp [left]) (by rw [ah]; simp [right]) asafe.2 hend
  dsimp only at ps
  obtain ⟨pairSafe, pairFit, p5, p6, framePair, pairPc, pairActive⟩ := ps
  let scanned := natRun rom containing (RawCandidatePairScan.totalSteps full.length (order node) later q) arguments
  have sf (address : Nat) (ha : 8 ≤ address) : scanned.heap address = state.heap address :=
    (framePair address ha).trans (aframe address ha)
  have st : InputTables q full B nodes order inverse scanned := tables_of_heap_above tables sf
  have sk : scanned.heap (B + 1) = node := (sf _ (by omega)).trans hnode
  have sj : scanned.heap (B + 2) = later := (sf _ (by omega)).trans hlater
  have bestFit : Fits (indexWidth 32 full.length q) (scanned.heap (B + 3)) := by
    rw [sf _ (by omega)]
    apply small_fits
    exact hbest.trans (by dsimp [M, candidateCount]; omega)
  have parentFit : Fits (indexWidth 32 full.length q)
      (scanned.heap (parentSlot B M (scanned.heap (B + 1)))) := by
    rw [sk, sf _ (by unfold parentSlot arraySlot; omega)]
    exact hparent
  have tm := PA06A19PrepareCompactParents035Pieces.innerTail_safe q full start scanned pairFit st.base_cell st.count_cell
    (by rw [sk]; exact hn.le.trans ht) (by rw [sj]; exact hj.le)
    (small_fits _ _ _ (p5.trans (by dsimp [candidateCount]; omega)))
    (small_fits _ _ _ (p6.trans (by dsimp [candidateCount]; omega)))
    (by rw [sj]; exact keep_word_fits st later hj)
    (by rw [sj]; exact card_word_fits st later hj) bestFit
    (by rw [sj]; exact inverse_word_fits st hinverse later hj) parentFit hend
  have ts := chunk_of_macro q full containing start hbound hcode .innerTail scanned pairPc pairActive tm
  dsimp only [chunkLength] at ss asafe ts
  have runTest : natRun rom containing 13 state = tested := chunk_run q full containing start hbound hcode .innerTest state hpc ha
  have runArgs : natRun rom containing 28 tested = arguments := chunk_run q full containing start hbound hcode .pairArgs tested tp ta
  have pairRest : PrefixSafe (SafePoint q full containing start) rom containing arguments
      (RawCandidatePairScan.totalSteps full.length (order node) later q + 116) := PrefixSafe.add _ _ _ _ _ _ pairSafe ts.1
  have argRest : PrefixSafe (SafePoint q full containing start) rom containing tested
      (28 + (RawCandidatePairScan.totalSteps full.length (order node) later q + 116)) := by
    apply PrefixSafe.add _ _ _ _ _ _ asafe.1
    rw [runArgs]
    exact pairRest
  have hclock : innerIterationSteps full.length q (order node) later =
      13 + (28 + (RawCandidatePairScan.totalSteps full.length (order node) later q + 116)) := by
    unfold innerIterationSteps
    omega
  constructor
  · rw [hclock]
    apply PrefixSafe.add _ _ _ _ _ _ ss.1
    rw [runTest]
    exact argRest
  · rw [hclock, natRun_add, runTest, natRun_add, runArgs, natRun_add]
    exact ts.2

theorem inner_scan_partial_safe (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (16) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (node : Nat) (hn : node < nodes)
    (hnode : state.heap (16 + 1) = node)
    (hlater : state.heap (16 + 2) = 0)
    (hbest : state.heap (16 + 3) ≤ q + 1)
    (hparent : Fits (indexWidth 32 full.length q)
      (state.heap (parentSlot (16) (candidateCount full.length q) node)))
    (hpc : state.pc = 5 * (start + 64)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361)))
    (count : Nat) (hc : count ≤ candidateCount full.length q) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (innerScanSteps full.length q (order node) count) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (innerScanSteps full.length q (order node) count) state) := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [innerScanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 0 ∧
        RegistersFit (indexWidth 32 full.length q) state from ⟨by intro clock hc; omega, hf⟩)
  | succ count ih =>
    intro hc
    obtain ⟨safe, fits⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing (innerScanSteps full.length q (order node) count) state
    have data := inner_scan_partial_wordData q full containing start hbound hcode nodes order inverse state tables hinverse
      node hn hnode hlater hbest hparent hpc ha count (by omega)
    dsimp only at data
    obtain ⟨pt, pn, pj, pb, pp, pc, pa⟩ := data
    have step := inner_iteration_safe q full containing start hbound hcode nodes order inverse previous pt hinverse
      node count hn (by omega) pn pj pb pp pc pa fits hend
    constructor
    · rw [innerScanSteps_succ]
      exact PrefixSafe.add _ _ _ _ _ _ safe step.1
    · rw [innerScanSteps_succ, natRun_add]
      exact step.2

theorem inner_scan_safe (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (16) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (node : Nat) (hn : node < nodes)
    (hnode : state.heap (16 + 1) = node)
    (hlater : state.heap (16 + 2) = 0)
    (hbest : state.heap (16 + 3) ≤ q + 1)
    (hparent : Fits (indexWidth 32 full.length q)
      (state.heap (parentSlot (16) (candidateCount full.length q) node)))
    (hpc : state.pc = 5 * (start + 64)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (innerCompleteSteps full.length q (order node)) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (innerCompleteSteps full.length q (order node)) state) := by
  let M := candidateCount full.length q
  have ss := inner_scan_partial_safe q full containing start hbound hcode nodes order inverse state tables hinverse
    node hn hnode hlater hbest hparent hpc ha hf hend M le_rfl
  have data := inner_scan_partial_wordData q full containing start hbound hcode nodes order inverse state tables hinverse
    node hn hnode hlater hbest hparent hpc ha M le_rfl
  dsimp only at data
  obtain ⟨pt, _pn, pj, _pb, _pp, pc, pa⟩ := data
  let previous := natRun (rawIncidenceROM q full) containing (innerScanSteps full.length q (order node) M) state
  have ts := chunk_of_macro q full containing start hbound hcode .innerTest previous pc pa
    (PA06A19PrepareCompactOrdering034Macros.testWorkspace_safe q full 2 (start + 346) (by omega) previous ss.2 pt.base_cell
      (by rw [pt.count_cell]; exact count_fits _ _)
      (by rw [pj]; exact count_fits _ _) (lt_of_le_of_lt (by omega) hend))
  dsimp only [chunkLength] at ts
  change PrefixSafe _ _ _ _ (innerScanSteps full.length q (order node) M + 13) ∧
    RegistersFit _ (natRun _ _ (innerScanSteps full.length q (order node) M + 13) _)
  constructor
  · exact PrefixSafe.add _ _ _ _ _ _ ss.1 ts.1
  · rw [natRun_add]
    exact ts.2

theorem outer_iteration_safe (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (16) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (node : Nat) (hn : node < nodes)
    (hnode : state.heap (16 + 1) = node)
    (hpc : state.pc = 5 * (start + 6)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (outerIterationSteps full.length q (order node)) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (outerIterationSteps full.length q (order node)) state) := by
  let rom := rawIncidenceROM q full
  let B := 16
  let M := candidateCount full.length q
  have hb : 16 ≤ B := (show 16 ≤ 16 from le_rfl)
  have ht : nodes ≤ M := tables.nodes_le
  let tested := runOps rom (outerTest (start + 361)) state
  have tv := outerTest_values rom (start + 361) state
  have th : tested.heap = state.heap := tv.1
  have tp : tested.pc = 5 * (start + 27) := by
    have hp := tv.2.1
    rw [tables.base_cell, tables.count_cell, tables.node_count, hnode,
      ite_eq_right (Nat.sub_ne_zero_of_lt hn), hpc] at hp
    change tested.pc = _ at hp
    omega
  have ta : tested.halted = false := tv.2.2.trans ha
  have tt := tables_of_heap_eq tables th
  have nc : state.heap (nodeCountAddress B M) = nodes := tables.node_count
  have ts := chunk_of_macro q full containing start hbound hcode .outerTest state hpc ha
    (PA06A19PrepareCompactParents035Pieces.outerTest_safe q full (start + 361) state hf tables.base_cell tables.count_cell
      (by rw [hnode]; exact hn.le.trans ht)
      (by change state.heap (nodeCountAddress B M) ≤ M; rw [nc]; exact ht) hend)
  rw [chunk_run q full containing start hbound hcode .outerTest state hpc ha] at ts
  let prepared := natRun rom containing 37 tested
  have ini := chunk_of_macro q full containing start hbound hcode .initializeChild tested tp ta
    (PA06A19PrepareCompactParents035Pieces.initializeChild_safe q full tested ts.2 tt.base_cell tt.count_cell
      (by rw [th, hnode]; exact hn.le.trans ht))
  have idata := RawCandidateParentRAM.initialize_child q full containing start hbound hcode B nodes order inverse
    tested hb tt node hn (by rw [th]; exact hnode) tp ta
  dsimp only at idata
  obtain ⟨it, ik, ij, ib, ipar, _iframe, pcInit, activeInit⟩ := idata
  have initParent : Fits (indexWidth 32 full.length q) (prepared.heap (parentSlot B M node)) := by
    have value : prepared.heap (parentSlot B M node) = 0 := ipar
    rw [value]
    exact zero_fits _ _
  have scan := inner_scan_safe q full containing start hbound hcode nodes order inverse prepared it hinverse
    node hn ik ij ib.le initParent pcInit activeInit ini.2 hend
  have sd := inner_scan_wordData q full containing start hbound hcode nodes order inverse prepared it hinverse
    node hn ik ij ib.le initParent pcInit activeInit
  dsimp only at sd
  obtain ⟨st, sk, _sj, _sb, _sp, pcScan, activeScan⟩ := sd
  let scanned := natRun rom containing (innerCompleteSteps full.length q (order node)) prepared
  have tm := PA06A19PrepareCompactParents035Pieces.outerTail_safe q full start scanned scan.2 st.base_cell
    (by rw [sk]; exact hn.le.trans ht) hend
  have tail := chunk_of_macro q full containing start hbound hcode .outerTail scanned pcScan activeScan tm
  dsimp only [chunkLength] at ts ini tail
  have runTest : natRun rom containing 21 state = tested := chunk_run q full containing start hbound hcode .outerTest state hpc ha
  have scanRest : PrefixSafe (SafePoint q full containing start) rom containing prepared
      (innerCompleteSteps full.length q (order node) + 15) := PrefixSafe.add _ _ _ _ _ _ scan.1 tail.1
  have initRest : PrefixSafe (SafePoint q full containing start) rom containing tested
      (37 + (innerCompleteSteps full.length q (order node) + 15)) := PrefixSafe.add _ _ _ _ _ _ ini.1 scanRest
  have hclock : outerIterationSteps full.length q (order node) =
      21 + (37 + (innerCompleteSteps full.length q (order node) + 15)) := by unfold outerIterationSteps; omega
  constructor
  · rw [hclock]
    apply PrefixSafe.add _ _ _ _ _ _ ts.1
    rw [runTest]
    exact initRest
  · rw [hclock, natRun_add, runTest, natRun_add]
    change RegistersFit _ (natRun rom containing (innerCompleteSteps full.length q (order node) + 15) prepared)
    rw [natRun_add]
    exact tail.2

theorem outer_scan_partial_safe (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (16) nodes order inverse state)
    (hinverse : InverseFits q full inverse)
    (hnode : state.heap (16 + 1) = 0)
    (hpc : state.pc = 5 * (start + 6)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361)))
    (count : Nat) (hc : count ≤ nodes) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (outerScanSteps full.length q order count) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (outerScanSteps full.length q order count) state) := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [outerScanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 0 ∧
        RegistersFit (indexWidth 32 full.length q) state from ⟨by intro clock hc; omega, hf⟩)
  | succ count ih =>
    intro hc
    obtain ⟨safe, fits⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing (outerScanSteps full.length q order count) state
    have data := RawCandidateParentRAM.outer_scan_partial q full containing start hbound hcode (16)
      nodes order inverse state ((show 16 ≤ 16 from le_rfl)) tables hnode hpc ha count (by omega)
    dsimp only at data
    obtain ⟨pt, pn, _parents, _frame, pc, pa⟩ := data
    have step := outer_iteration_safe q full containing start hbound hcode nodes order inverse previous pt hinverse
      count (by omega) pn pc pa fits hend
    constructor
    · rw [outerScanSteps_succ]
      exact PrefixSafe.add _ _ _ _ _ _ safe step.1
    · rw [outerScanSteps_succ, natRun_add]
      exact step.2

/-- Complete real parent-loop safety.  Initial parent slots, counters,
and scratch cells are not assumed to contain answers or valid words. -/
theorem parents_nat_safe (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (16) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (totalSteps full.length q nodes order) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (totalSteps full.length q nodes order) state) := by
  let rom := rawIncidenceROM q full
  let B := 16
  let M := candidateCount full.length q
  have hb : 16 ≤ B := (show 16 ≤ 16 from le_rfl)
  let initialized := runOps rom (RawCandidateOrderingRAM.setWorkspace 1 0) state
  have ini := chunk_of_macro q full containing start hbound hcode .initialize state
    (by simpa only [chunkOffset, Nat.add_zero] using hpc) ha
    (PA06A19PrepareCompactOrdering034Macros.setWorkspace_safe q full 1 0 (by omega) state hf tables.base_cell (zero_fits _ _))
  rw [chunk_run q full containing start hbound hcode .initialize state
    (by simpa only [chunkOffset, Nat.add_zero] using hpc) ha] at ini
  have ih : initialized.heap = Function.update state.heap (B + 1) 0 := by
    simpa only [tables.base_cell] using RawCandidateParentRAM.setWorkspace_heap rom 1 0 state
  have it : InputTables q full B nodes order inverse initialized :=
    tables.transport q full B nodes order inverse state initialized hb (fun address hp => by rw [ih]; exact Function.update_of_ne hp.2.1 _ _)
  have ik : initialized.heap (B + 1) = 0 := by rw [ih]; simp
  have ip : initialized.pc = 5 * (start + 6) := by
    rw [show initialized = runOps rom (RawCandidateOrderingRAM.setWorkspace 1 0) state from rfl,
      runOps_pc rom (RawCandidateOrderingRAM.setWorkspace 1 0) state (by
        simp [RawCandidateOrderingRAM.setWorkspace, RawCandidateOrderingRAM.storeWorkspace, loadCell, NoJump]),
      RawCandidateParentRAM.setWorkspace_length, hpc]
    omega
  have ia : initialized.halted = false := (runOps_halted _ _ _).trans ha
  have ss := outer_scan_partial_safe q full containing start hbound hcode nodes order inverse initialized it hinverse ik ip ia ini.2 hend nodes le_rfl
  have data := RawCandidateParentRAM.outer_scan_partial q full containing start hbound hcode B nodes order inverse initialized hb
    it ik ip ia nodes le_rfl
  dsimp only at data
  obtain ⟨pt, pn, _parents, _frame, pc, pa⟩ := data
  let previous := natRun rom containing (outerScanSteps full.length q order nodes) initialized
  have ht : nodes ≤ M := tables.nodes_le
  have nc : previous.heap (nodeCountAddress B M) = nodes := pt.node_count
  have ts := chunk_of_macro q full containing start hbound hcode .outerTest previous pc pa
    (PA06A19PrepareCompactParents035Pieces.outerTest_safe q full (start + 361) previous ss.2 pt.base_cell pt.count_cell
      (by rw [pn]; exact ht)
      (by change previous.heap (nodeCountAddress B M) ≤ M; rw [nc]; exact ht) hend)
  dsimp only [chunkLength] at ini ts
  have runInit : natRun rom containing 6 state = initialized := chunk_run q full containing start hbound hcode .initialize state
    (by simpa only [chunkOffset, Nat.add_zero] using hpc) ha
  have body : PrefixSafe (SafePoint q full containing start) rom containing initialized
      (outerScanSteps full.length q order nodes + 21) := PrefixSafe.add _ _ _ _ _ _ ss.1 ts.1
  have hclock : totalSteps full.length q nodes order = 6 + (outerScanSteps full.length q order nodes + 21) := by unfold totalSteps; omega
  constructor
  · rw [hclock]
    apply PrefixSafe.add _ _ _ _ _ _ ini.1
    rw [runInit]
    exact body
  · rw [hclock, natRun_add, runInit, natRun_add]
    exact ts.2

theorem natRun_prefix_safe (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (16) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361)))
    (count : Nat) (hc : count ≤ totalSteps full.length q nodes order) :
    let result := natRun (rawIncidenceROM q full) containing count state
    RegistersFit (indexWidth 32 full.length q) result ∧ Fits (indexWidth 32 full.length q) result.pc ∧ result.halted = false := by
  have ss := parents_nat_safe q full containing start hbound hcode nodes order inverse state tables hinverse hpc ha hf hend
  by_cases heq : count = totalSteps full.length q nodes order
  · subst count
    have data := parents_wordData q full containing start hbound hcode nodes order inverse state tables hinverse hpc ha
    exact ⟨ss.2, by rw [data.2.2.1]; exact hend, data.2.2.2⟩
  · have point := ss.1 count (by omega)
    exact ⟨point.1, point.pcFits hend, point.2.choose_spec.2.2.1⟩

omit hbound hcode in
private theorem input_prefix (initialUsed : Finset (Fin q)) :
    PA06A19PrepareROM001.ROMPrefix (rawIncidenceROM q full)
      (CompactControllerClaims.controllerInput q full initialUsed) :=
  PA06A19PrepareROM001.inputTail_prefix _
    ((List.finRange q).map (fun tool => bit (decide (tool ∈ initialUsed))))

theorem word_run_eq_nat (initialUsed : Finset (Fin q))
    (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full 16 nodes order inverse state)
    (hinverse : InverseFits q full inverse) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361)))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ totalSteps full.length q nodes order) :
    packingRun (CompactControllerClaims.controllerInput q full initialUsed) containing count
      (state.toWord (indexWidth 32 full.length q)) =
        (natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 32 full.length q) := by
  have safe := parents_nat_safe q full containing start hbound hcode nodes order inverse state tables hinverse hpc ha hf hend
  have rawEq (k : Nat) (hk : k ≤ totalSteps full.length q nodes order) :
      natRun (CompactControllerClaims.controllerInput q full initialUsed) containing k state =
        natRun (rawIncidenceROM q full) containing k state := by
    apply PA06A19PrepareROM001.natRun_eq_of_romPrefix (input_prefix q full initialUsed) (linearLimit full.length q)
    intro clock hclock _active op decoded
    obtain ⟨_registers, _offset, _bound, _pc, _active, actualOp, hd, access⟩ := safe.1 clock (by omega)
    have hop : op = actualOp := Option.some.inj (decoded.symm.trans hd)
    subst op
    exact access
  have word := natRun_toWord (CompactControllerClaims.controllerInput q full initialUsed) containing state count hwords (by
    intro clock hclock
    rw [rawEq clock (by omega)]
    have point := safe.1 clock (by omega)
    exact ⟨point.1, point.pcFits hend⟩)
  exact word.trans (congrArg (NatState.toWord (indexWidth 32 full.length q)) (rawEq count hc))

theorem word_prefix_safe (initialUsed : Finset (Fin q))
    (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full 16 nodes order inverse state)
    (hinverse : InverseFits q full inverse) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361)))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode containing))
    (count : Nat) (hc : count < totalSteps full.length q nodes order) :
    let runtime := CompactControllerClaims.controllerInput q full initialUsed
    let actual := packingRun runtime containing count (state.toWord (indexWidth 32 full.length q))
    actual.halted = false ∧ actual.pc.toNat + 4 < (packingCode containing).length ∧
      ∃ op, PackingOp.decode (fetch containing actual) = some op ∧ packingAccessFits runtime (linearLimit full.length q) actual op := by
  have point := (parents_nat_safe q full containing start hbound hcode nodes order inverse state tables hinverse hpc ha hf hend).1 count hc
  have pcFit := point.pcFits hend
  obtain ⟨registers, offset, hoff, pc, active, op, decoded, access⟩ := point
  dsimp only
  rw [word_run_eq_nat q full containing start hbound hcode initialUsed nodes order inverse state
    tables hinverse hpc ha hf hend hwords count hc.le]
  have wordPC : ((natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 32 full.length q)).pc.toNat =
      5 * (start + offset) := by
    change (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit, pc]
  refine ⟨active, ?_, op, ?_, ?_⟩
  · rw [wordPC, packingCode_length]
    omega
  · change PackingOp.decode (physicalFetch _ (packingCode containing)
      ((natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 32 full.length q)).pc.toNat) = _
    rw [wordPC, physicalFetch_eq _ _ _ hwords]
    change PackingOp.decode (natFetch containing (5 * (start + offset))) = some op
    simpa only [pc] using decoded
  · apply physical_access_of_nat (CompactControllerClaims.controllerInput q full initialUsed) (linearLimit full.length q) _ _ registers
    cases op with
    | base instruction =>
      exact PA06A19PrepareROM001.accessFits_of_romPrefix (input_prefix q full initialUsed) (linearLimit full.length q) _ instruction
        (by simpa only [RawIncidenceScanSafety.NatAccessFits,
          PA06A19PrepareCompactParents035Safety.linearLimit] using access)
    | arithmetic operation target left right => trivial
    | jumpIfZero condition target => trivial

/-- Exact parent data from the unchanged Nat search, on the same actual
Word run and controller input as the all-clock physical safety theorem. -/
theorem parents_word (initialUsed : Finset (Fin q))
    (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full 16 nodes order inverse state)
    (hinverse : InverseFits q full inverse) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361)))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode containing)) :
    let result := natRun (rawIncidenceROM q full) containing (totalSteps full.length q nodes order) state
    packingRun (CompactControllerClaims.controllerInput q full initialUsed) containing (totalSteps full.length q nodes order)
        (state.toWord (indexWidth 32 full.length q)) = result.toWord (indexWidth 32 full.length q) ∧
      InputTables q full 16 nodes order inverse result ∧
      (∀ node < nodes, result.heap (parentSlot 16 (candidateCount full.length q) node) =
        RawCandidateParentScan.bestEncoded q full inverse (order node) (candidateCount full.length q)) ∧
      result.pc = 5 * (start + 361) ∧ result.halted = false := by
  have data := RawCandidateParentRAM.parents q full containing start hbound hcode 16 nodes
    order inverse state (by decide) tables hpc ha
  dsimp only at data ⊢
  obtain ⟨outputTables, _endCounter, parents, _frame, pc, active⟩ := data
  exact ⟨word_run_eq_nat q full containing start hbound hcode initialUsed nodes order inverse state tables hinverse
    hpc ha hf hend hwords _ le_rfl, outputTables, parents, pc, active⟩

/-- The real sorting output, rather than a supplied inverse bound,
qualifies the complete parent Word loop. -/
theorem parents_of_sorted_word (initialUsed : Finset (Fin q))
    (sortStart : Nat) (before state : NatState)
    (sorted : RawCandidateOrderingRAM.Sorted q full 16 sortStart before state)
    (hq : 0 < q) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361)))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode containing)) :
    let nodes := (RawCandidateOrder.retainedCandidateIndices q full).length
    let order := observedOrder q full 16 state
    let inverse := observedInverse q full 16 state
    let result := natRun (rawIncidenceROM q full) containing (totalSteps full.length q nodes order) state
    packingRun (CompactControllerClaims.controllerInput q full initialUsed) containing (totalSteps full.length q nodes order)
        (state.toWord (indexWidth 32 full.length q)) = result.toWord (indexWidth 32 full.length q) ∧
      InputTables q full 16 nodes order inverse result ∧
      (∀ node < nodes, result.heap (parentSlot 16 (candidateCount full.length q) node) =
        RawCandidateParentScan.bestEncoded q full inverse (order node) (candidateCount full.length q)) ∧
      result.pc = 5 * (start + 361) ∧ result.halted = false :=
  parents_word q full containing start hbound hcode initialUsed _ _ _ state
    (InputTables.of_sorted q full _ sortStart before state sorted hq)
    (inverseFits_of_sorted q full sortStart before state sorted) hpc ha hf hend hwords

end Linked

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Loop


