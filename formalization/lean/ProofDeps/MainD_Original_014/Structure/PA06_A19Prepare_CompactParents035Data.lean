module

public import Structure.PA06_A19Prepare_CompactParents035Safety
public import PaperProofs.Structure.RawCandidateParentWord

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Ordinary source-word data at real boundaries of the unchanged361-op
parent search, at B16/full width32. The original Nat transitions, table
transport and bestEncoded equations discharge each updated word bound.
No chosen parent, previous Fit16, or completed safe execution is assumed. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Data

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateParentRAM
open RawCandidateOrderingRAM (arraySlot testWorkspace testWorkspace_effect)
open RawCandidateWorkspaceInit (candidateCount)
open RawCandidateParentWordChunks (Chunk chunkCode chunkOffset chunkLength)
open PA06A19PrepareCompactParents035Safety (SafePoint)
open PA06A19PrepareCompactOrdering034Macros (MacroSafe)
open RawCandidateParentWord (candidateCard_le bestCard_le)

theorem count_fits (N q : Nat) : Fits (indexWidth 32 N q) (candidateCount N q) :=
  PA06A19PrepareCompactArrays018.value_le_count_fits N q _ le_rfl
def InverseFits (q : Nat) (full : List (Finset (Fin q))) (inverse : Nat → Nat) : Prop :=
  ∀ index < candidateCount full.length q, Fits (indexWidth 32 full.length q) (inverse index)

theorem zero_fits (N q : Nat) : Fits (indexWidth 32 N q) 0 :=
  (Nat.zero_le (candidateCount N q)).trans_lt (count_fits N q)

theorem bestEncoded_fits (q : Nat) (full : List (Finset (Fin q))) (inverse : Nat → Nat)
    (hinverse : InverseFits q full inverse) (child upto : Nat) (hupto : upto ≤ candidateCount full.length q) :
    Fits (indexWidth 32 full.length q) (RawCandidateParentScan.bestEncoded q full inverse child upto) := by
  revert hupto
  induction upto with
  | zero => intro _; rw [RawCandidateParentScan.bestEncoded_zero]; exact zero_fits _ _
  | succ upto ih =>
    intro hupto
    rw [RawCandidateParentScan.bestEncoded_succ]
    split
    · exact hinverse upto (by omega)
    · exact ih (by omega)

theorem inverseFits_of_sorted (q : Nat) (full : List (Finset (Fin q))) (sortStart : Nat)
    (before state : NatState)
    (sorted : RawCandidateOrderingRAM.Sorted q full (16) sortStart before state) :
    InverseFits q full (observedInverse q full (16) state) := by
  intro index hi
  have value : observedInverse q full (16) state index =
      if RawCandidateOrder.keepCandidate q full index then RawCandidateRankPositions.lessCount q full index + 1 else 0 :=
    sorted.output.inverse index hi
  rw [value]
  split
  · exact (Nat.succ_le_of_lt (RawCandidateRankScan.lessCount_lt_candidateCount q full index hi)).trans_lt
      (count_fits full.length q)
  · exact zero_fits _ _

theorem tables_of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {before after : NatState}
    (tables : RawCandidateParentRAM.InputTables q full (16) nodes order inverse before)
    (hh : after.heap = before.heap) :
    RawCandidateParentRAM.InputTables q full (16) nodes order inverse after :=
  tables.transport q full _ nodes order inverse before after ((show 16 ≤ 16 from le_rfl)) (fun address _ => congrFun hh address)

theorem tables_of_heap_above {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {before after : NatState}
    (tables : RawCandidateParentRAM.InputTables q full (16) nodes order inverse before)
    (frame : ∀ address, 8 ≤ address → after.heap address = before.heap address) :
    RawCandidateParentRAM.InputTables q full (16) nodes order inverse after :=
  tables.transport q full _ nodes order inverse before after ((show 16 ≤ 16 from le_rfl)) (fun address hp => frame address hp.1)

theorem nodeCount_word_fits {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {state : NatState}
    (tables : RawCandidateParentRAM.InputTables q full (16) nodes order inverse state) :
    Fits (indexWidth 32 full.length q)
      (state.heap (nodeCountAddress (16) (candidateCount full.length q))) := by
  have value : state.heap (nodeCountAddress (16) (candidateCount full.length q)) = nodes := tables.node_count
  rw [value]
  exact tables.nodes_le.trans_lt (count_fits _ _)

theorem card_word_fits {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {state : NatState}
    (tables : RawCandidateParentRAM.InputTables q full (16) nodes order inverse state)
    (index : Nat) (hi : index < candidateCount full.length q) :
    Fits (indexWidth 32 full.length q)
      (state.heap (arraySlot (16) (candidateCount full.length q) 0 index)) := by
  have value : state.heap (arraySlot (16) (candidateCount full.length q) 0 index) =
      RawCandidateStableOrder.candidateCard q full index := tables.cards index hi
  rw [value]
  exact ((candidateCard_le q full index).trans (show q ≤ candidateCount full.length q by dsimp [candidateCount]; omega)).trans_lt
    (count_fits _ _)

theorem keep_word_fits {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {state : NatState}
    (tables : RawCandidateParentRAM.InputTables q full (16) nodes order inverse state)
    (index : Nat) (hi : index < candidateCount full.length q) :
    Fits (indexWidth 32 full.length q)
      (state.heap (arraySlot (16) (candidateCount full.length q) 1 index)) := by
  have value : state.heap (arraySlot (16) (candidateCount full.length q) 1 index) =
      bit (RawCandidateOrder.keepCandidate q full index) := tables.keeps index hi
  rw [value]
  have bound : bit (RawCandidateOrder.keepCandidate q full index) ≤ candidateCount full.length q := by
    cases RawCandidateOrder.keepCandidate q full index <;> simp only [bit, Bool.false_eq_true, ite_false, ite_true]
    · omega
    · dsimp [candidateCount]; omega
  exact bound.trans_lt (count_fits _ _)

theorem order_word_fits {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {state : NatState}
    (tables : RawCandidateParentRAM.InputTables q full (16) nodes order inverse state)
    (node : Nat) (hn : node < nodes) :
    Fits (indexWidth 32 full.length q)
      (state.heap (arraySlot (16) (candidateCount full.length q) 2 node)) := by
  have value : state.heap (arraySlot (16) (candidateCount full.length q) 2 node) = order node := tables.ordered node hn
  rw [value]
  exact (tables.order_valid node hn).le.trans_lt (count_fits _ _)

theorem inverse_word_fits {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {state : NatState}
    (tables : RawCandidateParentRAM.InputTables q full (16) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (index : Nat) (hi : index < candidateCount full.length q) :
    Fits (indexWidth 32 full.length q)
      (state.heap (arraySlot (16) (candidateCount full.length q) 3 index)) := by
  have value : state.heap (arraySlot (16) (candidateCount full.length q) 3 index) = inverse index := tables.inverses index hi
  rw [value]
  exact hinverse index hi

theorem small_fits (N q value : Nat) (hv : value ≤ candidateCount N q) : Fits (indexWidth 32 N q) value :=
  hv.trans_lt (count_fits N q)

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 361 ≤ containing.length)
  (hcode : ∀ position < 361, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem chunk_run (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false) :
    natRun (rawIncidenceROM q full) containing (chunkLength chunk) state =
      runOps (rawIncidenceROM q full) (chunkCode start chunk) state := by
  rw [RawCandidateParentWordChunks.chunk_run_prefix _ containing start hbound hcode chunk state hpc ha (chunkLength chunk) le_rfl,
    List.take_of_length_le (by rw [RawCandidateParentWordChunks.chunk_code_length])]

theorem chunk_of_macro (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (hm : MacroSafe q full (chunkCode start chunk) state) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (chunkLength chunk) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength chunk) state) := by
  apply PA06A19PrepareCompactParents035Safety.chunk_safe q full containing start hbound hcode chunk state hpc ha
  · intro count hc
    exact hm.1 count (by rw [RawCandidateParentWordChunks.chunk_code_length]; exact hc)
  · intro count hc
    exact hm.2 count (by rw [RawCandidateParentWordChunks.chunk_code_length]; exact hc)

theorem pair_safe_data (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * (start + 105)) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361))) :
    let result := natRun (rawIncidenceROM q full) containing (RawCandidatePairScan.totalSteps full.length left.val right.val q) state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (RawCandidatePairScan.totalSteps full.length left.val right.val q) ∧
      RegistersFit (indexWidth 32 full.length q) result ∧ result.heap 5 ≤ q ∧ result.heap 6 ≤ q ∧
      (∀ address, 8 ≤ address → result.heap address = state.heap address) ∧
      result.pc = 5 * (start + 230) ∧ result.halted = false := by
  have ps := PA06A19PrepareCompactParents035Safety.pair_safe q full containing start hbound hcode left right state hpc ha hl hr hf hend
  have slice := RawCandidateParentWordSafety.pair_slice containing start hbound hcode
  have pn := RawCandidatePairScan.scan q full containing (start + 105) slice.1 slice.2 left right state hpc ha hl hr
  dsimp only at pn
  obtain ⟨_q, _cursor, _inter, h5, h6, frame, pc, active⟩ := pn
  have hcard (set : Finset (Fin q)) : set.card ≤ q := by simpa only [Fintype.card_fin] using Finset.card_le_univ set
  dsimp only
  refine ⟨ps.1, ps.2, ?_, ?_, ?_, ?_, active⟩
  · rw [h5]; exact hcard _
  · rw [h6]; exact hcard _
  · intro address ha
    exact frame address (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · omega

/-- Ordinary current-cell word bounds are preserved by one actual pair
query and strict-improvement update; no chosen-parent answer is supplied. -/
theorem inner_iteration_wordData (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (16) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (node later : Nat) (hn : node < nodes)
    (hj : later < candidateCount full.length q)
    (hnode : state.heap (16 + 1) = node)
    (hlater : state.heap (16 + 2) = later)
    (hbest : state.heap (16 + 3) ≤ q + 1)
    (hparent : Fits (indexWidth 32 full.length q)
      (state.heap (parentSlot (16) (candidateCount full.length q) node)))
    (hpc : state.pc = 5 * (start + 64)) (ha : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing (innerIterationSteps full.length q (order node) later) state
    InputTables q full (16) nodes order inverse result ∧
      result.heap (16 + 1) = node ∧
      result.heap (16 + 2) = later + 1 ∧
      result.heap (16 + 3) ≤ q + 1 ∧
      Fits (indexWidth 32 full.length q)
        (result.heap (parentSlot (16) (candidateCount full.length q) node)) ∧
      result.pc = 5 * (start + 64) ∧ result.halted = false := by
  let B := 16
  have hb : 16 ≤ B := (show 16 ≤ 16 from le_rfl)
  have hs := RawCandidateParentRAM.inner_iteration q full containing start hbound hcode B nodes order inverse state hb
    tables node later hn hj hnode hlater hpc ha
  dsimp only at hs
  obtain ⟨nt, nj, nb, np, frame, pc, active⟩ := hs
  dsimp only
  refine ⟨nt, (frame (B + 1) (by omega) (by omega) (by omega) (by unfold parentSlot arraySlot; omega)).trans hnode,
    nj, ?_, ?_, pc, active⟩
  · rw [nb]
    split
    · exact (candidateCard_le q full later).trans (Nat.le_succ q)
    · exact hbest
  · change Fits (indexWidth 32 full.length q)
      ((natRun (rawIncidenceROM q full) containing (innerIterationSteps full.length q (order node) later) state).heap
        (parentSlot B (full.length + q + 1) node))
    rw [np]
    split
    · exact hinverse later hj
    · exact hparent

/-- Bounds at every real inner-loop boundary, allowing arbitrary initial
best/parent words satisfying ordinary numerical bounds. -/
theorem inner_scan_partial_wordData (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (16) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (node : Nat) (hn : node < nodes)
    (hnode : state.heap (16 + 1) = node)
    (hlater : state.heap (16 + 2) = 0)
    (hbest : state.heap (16 + 3) ≤ q + 1)
    (hparent : Fits (indexWidth 32 full.length q)
      (state.heap (parentSlot (16) (candidateCount full.length q) node)))
    (hpc : state.pc = 5 * (start + 64)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ candidateCount full.length q) :
    let result := natRun (rawIncidenceROM q full) containing (innerScanSteps full.length q (order node) count) state
    InputTables q full (16) nodes order inverse result ∧
      result.heap (16 + 1) = node ∧
      result.heap (16 + 2) = count ∧
      result.heap (16 + 3) ≤ q + 1 ∧
      Fits (indexWidth 32 full.length q)
        (result.heap (parentSlot (16) (candidateCount full.length q) node)) ∧
      result.pc = 5 * (start + 64) ∧ result.halted = false := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [innerScanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show InputTables q full (16) nodes order inverse state ∧
        state.heap (16 + 1) = node ∧
        state.heap (16 + 2) = 0 ∧ state.heap (16 + 3) ≤ q + 1 ∧
        Fits (indexWidth 32 full.length q) (state.heap (parentSlot (16) (candidateCount full.length q) node)) ∧
        state.pc = 5 * (start + 64) ∧ state.halted = false from ⟨tables, hnode, hlater, hbest, hparent, hpc, ha⟩)
  | succ count ih =>
    intro hc
    obtain ⟨pt, pn, pj, pb, pp, pc, pa⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing (innerScanSteps full.length q (order node) count) state
    have step := inner_iteration_wordData q full containing start hbound hcode nodes order inverse previous pt hinverse
      node count hn (by omega) pn pj pb pp pc pa
    dsimp only
    rw [innerScanSteps_succ, natRun_add]
    exact step

theorem inner_scan_wordData (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (16) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (node : Nat) (hn : node < nodes)
    (hnode : state.heap (16 + 1) = node)
    (hlater : state.heap (16 + 2) = 0)
    (hbest : state.heap (16 + 3) ≤ q + 1)
    (hparent : Fits (indexWidth 32 full.length q)
      (state.heap (parentSlot (16) (candidateCount full.length q) node)))
    (hpc : state.pc = 5 * (start + 64)) (ha : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing (innerCompleteSteps full.length q (order node)) state
    InputTables q full (16) nodes order inverse result ∧
      result.heap (16 + 1) = node ∧
      result.heap (16 + 2) = candidateCount full.length q ∧
      result.heap (16 + 3) ≤ q + 1 ∧
      Fits (indexWidth 32 full.length q)
        (result.heap (parentSlot (16) (candidateCount full.length q) node)) ∧
      result.pc = 5 * (start + 346) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let B := 16
  let M := candidateCount full.length q
  have pn := inner_scan_partial_wordData q full containing start hbound hcode nodes order inverse state tables hinverse
    node hn hnode hlater hbest hparent hpc ha M le_rfl
  dsimp only at pn
  obtain ⟨pt, pk, pj, pb, pp, pc, pa⟩ := pn
  let previous := natRun rom containing (innerScanSteps full.length q (order node) M) state
  let tested := runOps rom (testWorkspace 2 (start + 346)) previous
  have ht := testWorkspace_effect rom 2 (start + 346) previous
  have th : tested.heap = previous.heap := ht.1
  have tp : tested.pc = 5 * (start + 346) := by
    have hp := ht.2.1
    rw [pt.base_cell, pt.count_cell, pj] at hp
    simp only [M, candidateCount, Nat.sub_self, ite_true] at hp
    exact hp
  have ta : tested.halted = false := ht.2.2.trans pa
  have runTest : natRun rom containing 13 previous = tested := chunk_run q full containing start hbound hcode .innerTest previous pc pa
  have whole : natRun rom containing (innerCompleteSteps full.length q (order node)) state = tested := by
    change natRun rom containing (innerScanSteps full.length q (order node) M + 13) state = tested
    rw [natRun_add, runTest]
  dsimp only
  rw [whole]
  exact ⟨tables_of_heap_eq pt th, (congrFun th _).trans pk, (congrFun th _).trans pj,
    (congrFun th _).le.trans pb, by rw [th]; exact pp, tp, ta⟩

theorem parents_wordData (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (16) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (hpc : state.pc = 5 * start) (ha : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing (totalSteps full.length q nodes order) state
    InputTables q full (16) nodes order inverse result ∧
      (∀ node < nodes, Fits (indexWidth 32 full.length q)
        (result.heap (parentSlot (16) (candidateCount full.length q) node))) ∧
      result.pc = 5 * (start + 361) ∧ result.halted = false := by
  have pn := RawCandidateParentRAM.parents q full containing start hbound hcode (16) nodes
    order inverse state ((show 16 ≤ 16 from le_rfl)) tables hpc ha
  dsimp only at pn
  obtain ⟨pt, _endCounter, parents, _frame, pc, active⟩ := pn
  dsimp only
  refine ⟨pt, ?_, pc, active⟩
  intro node hn
  have value : (natRun (rawIncidenceROM q full) containing (totalSteps full.length q nodes order) state).heap
      (parentSlot (16) (candidateCount full.length q) node) =
      RawCandidateParentScan.bestEncoded q full inverse (order node) (candidateCount full.length q) := parents node hn
  rw [value]
  exact bestEncoded_fits q full inverse hinverse (order node) _ le_rfl


end Linked

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Data

