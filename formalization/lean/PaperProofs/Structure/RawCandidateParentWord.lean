module

public import PaperProofs.Structure.RawCandidateParentRAM
public import PaperProofs.Structure.PackingWordRefinement
public import PaperProofs.Structure.RawCandidateWorkspaceBounds
public import PaperProofs.Structure.RawCandidateParentWordChunks
public import PaperProofs.Structure.RawCandidateParentWordSafety
public import PaperProofs.Structure.RawCandidateOrderingWord
public import PaperProofs.Structure.RawCandidateParentWordPieces

/-! Word-data invariants for the actual dynamic parent search.  Each
current parent cell is really initialized to zero before it is read;
inverse source words, rather than parent answers, are the handoff data. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateParentWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateParentRAM
open RawCandidateOrderingRAM (arraySlot testWorkspace testWorkspace_effect)
open RawCandidateWorkspaceInit (workspaceBase candidateCount workspaceBase_ge candidateCount_fits)
open RawCandidateParentWordChunks (Chunk chunkCode chunkOffset chunkLength)
open RawCandidateParentWordSafety (SafePoint)
open RawCandidateOrderingWord (MacroSafe)

def InverseFits (q : Nat) (full : List (Finset (Fin q))) (inverse : Nat → Nat) : Prop :=
  ∀ index < candidateCount full.length q, Fits (indexWidth 16 full.length q) (inverse index)

theorem zero_fits (N q : Nat) : Fits (indexWidth 16 N q) 0 :=
  (Nat.zero_le (candidateCount N q)).trans_lt (candidateCount_fits N q)

theorem candidateCard_le (q : Nat) (full : List (Finset (Fin q))) (index : Nat) :
    RawCandidateStableOrder.candidateCard q full index ≤ q := by
  have hh := Finset.card_le_univ ((RawCandidateOrder.candidateSupports q full).getD index ∅)
  simpa only [RawCandidateStableOrder.candidateCard, Fintype.card_fin] using hh

theorem bestCard_le (q : Nat) (full : List (Finset (Fin q))) (child upto : Nat) :
    RawCandidateParentScan.bestCard q full child upto ≤ q + 1 := by
  induction upto with
  | zero => rw [RawCandidateParentScan.bestCard_zero]
  | succ upto ih =>
    rw [RawCandidateParentScan.bestCard_succ]
    split
    · exact (candidateCard_le q full upto).trans (Nat.le_succ q)
    · exact ih

theorem bestEncoded_fits (q : Nat) (full : List (Finset (Fin q))) (inverse : Nat → Nat)
    (hinverse : InverseFits q full inverse) (child upto : Nat) (hupto : upto ≤ candidateCount full.length q) :
    Fits (indexWidth 16 full.length q) (RawCandidateParentScan.bestEncoded q full inverse child upto) := by
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
    (sorted : RawCandidateOrderingRAM.Sorted q full (workspaceBase full.length q) sortStart before state) :
    InverseFits q full (observedInverse q full (workspaceBase full.length q) state) := by
  intro index hi
  have value : observedInverse q full (workspaceBase full.length q) state index =
      if RawCandidateOrder.keepCandidate q full index then RawCandidateRankPositions.lessCount q full index + 1 else 0 :=
    sorted.output.inverse index hi
  rw [value]
  split
  · exact (Nat.succ_le_of_lt (RawCandidateRankScan.lessCount_lt_candidateCount q full index hi)).trans_lt
      (candidateCount_fits full.length q)
  · exact zero_fits _ _

theorem tables_of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {before after : NatState}
    (tables : RawCandidateParentRAM.InputTables q full (workspaceBase full.length q) nodes order inverse before)
    (hh : after.heap = before.heap) :
    RawCandidateParentRAM.InputTables q full (workspaceBase full.length q) nodes order inverse after :=
  tables.transport q full _ nodes order inverse before after (workspaceBase_ge _ _) (fun address _ => congrFun hh address)

theorem tables_of_heap_above {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {before after : NatState}
    (tables : RawCandidateParentRAM.InputTables q full (workspaceBase full.length q) nodes order inverse before)
    (frame : ∀ address, 8 ≤ address → after.heap address = before.heap address) :
    RawCandidateParentRAM.InputTables q full (workspaceBase full.length q) nodes order inverse after :=
  tables.transport q full _ nodes order inverse before after (workspaceBase_ge _ _) (fun address hp => frame address hp.1)

theorem nodeCount_word_fits {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {state : NatState}
    (tables : RawCandidateParentRAM.InputTables q full (workspaceBase full.length q) nodes order inverse state) :
    Fits (indexWidth 16 full.length q)
      (state.heap (nodeCountAddress (workspaceBase full.length q) (candidateCount full.length q))) := by
  have value : state.heap (nodeCountAddress (workspaceBase full.length q) (candidateCount full.length q)) = nodes := tables.node_count
  rw [value]
  exact tables.nodes_le.trans_lt (candidateCount_fits _ _)

theorem card_word_fits {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {state : NatState}
    (tables : RawCandidateParentRAM.InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (index : Nat) (hi : index < candidateCount full.length q) :
    Fits (indexWidth 16 full.length q)
      (state.heap (arraySlot (workspaceBase full.length q) (candidateCount full.length q) 0 index)) := by
  have value : state.heap (arraySlot (workspaceBase full.length q) (candidateCount full.length q) 0 index) =
      RawCandidateStableOrder.candidateCard q full index := tables.cards index hi
  rw [value]
  exact ((candidateCard_le q full index).trans (show q ≤ candidateCount full.length q by dsimp [candidateCount]; omega)).trans_lt
    (candidateCount_fits _ _)

theorem keep_word_fits {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {state : NatState}
    (tables : RawCandidateParentRAM.InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (index : Nat) (hi : index < candidateCount full.length q) :
    Fits (indexWidth 16 full.length q)
      (state.heap (arraySlot (workspaceBase full.length q) (candidateCount full.length q) 1 index)) := by
  have value : state.heap (arraySlot (workspaceBase full.length q) (candidateCount full.length q) 1 index) =
      bit (RawCandidateOrder.keepCandidate q full index) := tables.keeps index hi
  rw [value]
  have bound : bit (RawCandidateOrder.keepCandidate q full index) ≤ candidateCount full.length q := by
    cases RawCandidateOrder.keepCandidate q full index <;> simp only [bit, Bool.false_eq_true, ite_false, ite_true]
    · omega
    · dsimp [candidateCount]; omega
  exact bound.trans_lt (candidateCount_fits _ _)

theorem order_word_fits {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {state : NatState}
    (tables : RawCandidateParentRAM.InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (node : Nat) (hn : node < nodes) :
    Fits (indexWidth 16 full.length q)
      (state.heap (arraySlot (workspaceBase full.length q) (candidateCount full.length q) 2 node)) := by
  have value : state.heap (arraySlot (workspaceBase full.length q) (candidateCount full.length q) 2 node) = order node := tables.ordered node hn
  rw [value]
  exact (tables.order_valid node hn).le.trans_lt (candidateCount_fits _ _)

theorem inverse_word_fits {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {state : NatState}
    (tables : RawCandidateParentRAM.InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (index : Nat) (hi : index < candidateCount full.length q) :
    Fits (indexWidth 16 full.length q)
      (state.heap (arraySlot (workspaceBase full.length q) (candidateCount full.length q) 3 index)) := by
  have value : state.heap (arraySlot (workspaceBase full.length q) (candidateCount full.length q) 3 index) = inverse index := tables.inverses index hi
  rw [value]
  exact hinverse index hi

theorem small_fits (N q value : Nat) (hv : value ≤ candidateCount N q) : Fits (indexWidth 16 N q) value :=
  hv.trans_lt (candidateCount_fits N q)

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
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength chunk) state) := by
  apply RawCandidateParentWordSafety.chunk_safe q full containing start hbound hcode chunk state hpc ha
  · intro count hc
    exact hm.1 count (by rw [RawCandidateParentWordChunks.chunk_code_length]; exact hc)
  · intro count hc
    exact hm.2 count (by rw [RawCandidateParentWordChunks.chunk_code_length]; exact hc)

theorem pair_safe_data (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * (start + 105)) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 361))) :
    let result := natRun (rawIncidenceROM q full) containing (RawCandidatePairScan.totalSteps full.length left.val right.val q) state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (RawCandidatePairScan.totalSteps full.length left.val right.val q) ∧
      RegistersFit (indexWidth 16 full.length q) result ∧ result.heap 5 ≤ q ∧ result.heap 6 ≤ q ∧
      (∀ address, 8 ≤ address → result.heap address = state.heap address) ∧
      result.pc = 5 * (start + 230) ∧ result.halted = false := by
  have ps := RawCandidateParentWordSafety.pair_safe q full containing start hbound hcode left right state hpc ha hl hr hf hend
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
    (tables : InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (node later : Nat) (hn : node < nodes)
    (hj : later < candidateCount full.length q)
    (hnode : state.heap (workspaceBase full.length q + 1) = node)
    (hlater : state.heap (workspaceBase full.length q + 2) = later)
    (hbest : state.heap (workspaceBase full.length q + 3) ≤ q + 1)
    (hparent : Fits (indexWidth 16 full.length q)
      (state.heap (parentSlot (workspaceBase full.length q) (candidateCount full.length q) node)))
    (hpc : state.pc = 5 * (start + 64)) (ha : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing (innerIterationSteps full.length q (order node) later) state
    InputTables q full (workspaceBase full.length q) nodes order inverse result ∧
      result.heap (workspaceBase full.length q + 1) = node ∧
      result.heap (workspaceBase full.length q + 2) = later + 1 ∧
      result.heap (workspaceBase full.length q + 3) ≤ q + 1 ∧
      Fits (indexWidth 16 full.length q)
        (result.heap (parentSlot (workspaceBase full.length q) (candidateCount full.length q) node)) ∧
      result.pc = 5 * (start + 64) ∧ result.halted = false := by
  let B := workspaceBase full.length q
  have hb : 16 ≤ B := workspaceBase_ge _ _
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
  · change Fits (indexWidth 16 full.length q)
      ((natRun (rawIncidenceROM q full) containing (innerIterationSteps full.length q (order node) later) state).heap
        (parentSlot B (full.length + q + 1) node))
    rw [np]
    split
    · exact hinverse later hj
    · exact hparent

/-- Bounds at every real inner-loop boundary, allowing arbitrary initial
best/parent words satisfying ordinary numerical bounds. -/
theorem inner_scan_partial_wordData (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (node : Nat) (hn : node < nodes)
    (hnode : state.heap (workspaceBase full.length q + 1) = node)
    (hlater : state.heap (workspaceBase full.length q + 2) = 0)
    (hbest : state.heap (workspaceBase full.length q + 3) ≤ q + 1)
    (hparent : Fits (indexWidth 16 full.length q)
      (state.heap (parentSlot (workspaceBase full.length q) (candidateCount full.length q) node)))
    (hpc : state.pc = 5 * (start + 64)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ candidateCount full.length q) :
    let result := natRun (rawIncidenceROM q full) containing (innerScanSteps full.length q (order node) count) state
    InputTables q full (workspaceBase full.length q) nodes order inverse result ∧
      result.heap (workspaceBase full.length q + 1) = node ∧
      result.heap (workspaceBase full.length q + 2) = count ∧
      result.heap (workspaceBase full.length q + 3) ≤ q + 1 ∧
      Fits (indexWidth 16 full.length q)
        (result.heap (parentSlot (workspaceBase full.length q) (candidateCount full.length q) node)) ∧
      result.pc = 5 * (start + 64) ∧ result.halted = false := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [innerScanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show InputTables q full (workspaceBase full.length q) nodes order inverse state ∧
        state.heap (workspaceBase full.length q + 1) = node ∧
        state.heap (workspaceBase full.length q + 2) = 0 ∧ state.heap (workspaceBase full.length q + 3) ≤ q + 1 ∧
        Fits (indexWidth 16 full.length q) (state.heap (parentSlot (workspaceBase full.length q) (candidateCount full.length q) node)) ∧
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
    (tables : InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (node : Nat) (hn : node < nodes)
    (hnode : state.heap (workspaceBase full.length q + 1) = node)
    (hlater : state.heap (workspaceBase full.length q + 2) = 0)
    (hbest : state.heap (workspaceBase full.length q + 3) ≤ q + 1)
    (hparent : Fits (indexWidth 16 full.length q)
      (state.heap (parentSlot (workspaceBase full.length q) (candidateCount full.length q) node)))
    (hpc : state.pc = 5 * (start + 64)) (ha : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing (innerCompleteSteps full.length q (order node)) state
    InputTables q full (workspaceBase full.length q) nodes order inverse result ∧
      result.heap (workspaceBase full.length q + 1) = node ∧
      result.heap (workspaceBase full.length q + 2) = candidateCount full.length q ∧
      result.heap (workspaceBase full.length q + 3) ≤ q + 1 ∧
      Fits (indexWidth 16 full.length q)
        (result.heap (parentSlot (workspaceBase full.length q) (candidateCount full.length q) node)) ∧
      result.pc = 5 * (start + 346) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
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
    (tables : InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (hpc : state.pc = 5 * start) (ha : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing (totalSteps full.length q nodes order) state
    InputTables q full (workspaceBase full.length q) nodes order inverse result ∧
      (∀ node < nodes, Fits (indexWidth 16 full.length q)
        (result.heap (parentSlot (workspaceBase full.length q) (candidateCount full.length q) node))) ∧
      result.pc = 5 * (start + 361) ∧ result.halted = false := by
  have pn := RawCandidateParentRAM.parents q full containing start hbound hcode (workspaceBase full.length q) nodes
    order inverse state (workspaceBase_ge _ _) tables hpc ha
  dsimp only at pn
  obtain ⟨pt, _endCounter, parents, _frame, pc, active⟩ := pn
  dsimp only
  refine ⟨pt, ?_, pc, active⟩
  intro node hn
  have value : (natRun (rawIncidenceROM q full) containing (totalSteps full.length q nodes order) state).heap
      (parentSlot (workspaceBase full.length q) (candidateCount full.length q) node) =
      RawCandidateParentScan.bestEncoded q full inverse (order node) (candidateCount full.length q) := parents node hn
  rw [value]
  exact bestEncoded_fits q full inverse hinverse (order node) _ le_rfl

theorem inner_iteration_safe (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (node later : Nat) (hn : node < nodes)
    (hj : later < candidateCount full.length q)
    (hnode : state.heap (workspaceBase full.length q + 1) = node)
    (hlater : state.heap (workspaceBase full.length q + 2) = later)
    (hbest : state.heap (workspaceBase full.length q + 3) ≤ q + 1)
    (hparent : Fits (indexWidth 16 full.length q)
      (state.heap (parentSlot (workspaceBase full.length q) (candidateCount full.length q) node)))
    (hpc : state.pc = 5 * (start + 64)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 361))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (innerIterationSteps full.length q (order node) later) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (innerIterationSteps full.length q (order node) later) state) := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  have hb : 16 ≤ B := workspaceBase_ge _ _
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
    (RawCandidateOrderingWord.testWorkspace_safe q full 2 (start + 346) (by omega) state hf tables.base_cell
      (by rw [tables.count_cell]; exact candidateCount_fits _ _)
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
    (RawCandidateParentWordPieces.pairArguments_safe q full tested ss.2 tt.base_cell tt.count_cell
      (by rw [th, hnode]; omega) (by rw [th, hlater]; exact hj.le)
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
  have bestFit : Fits (indexWidth 16 full.length q) (scanned.heap (B + 3)) := by
    rw [sf _ (by omega)]
    apply small_fits
    exact hbest.trans (by dsimp [M, candidateCount]; omega)
  have parentFit : Fits (indexWidth 16 full.length q)
      (scanned.heap (parentSlot B M (scanned.heap (B + 1)))) := by
    rw [sk, sf _ (by unfold parentSlot arraySlot; omega)]
    exact hparent
  have tm := RawCandidateParentWordPieces.innerTail_safe q full start scanned pairFit st.base_cell st.count_cell
    (by rw [sk]; omega) (by rw [sj]; exact hj.le)
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
    (tables : InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (node : Nat) (hn : node < nodes)
    (hnode : state.heap (workspaceBase full.length q + 1) = node)
    (hlater : state.heap (workspaceBase full.length q + 2) = 0)
    (hbest : state.heap (workspaceBase full.length q + 3) ≤ q + 1)
    (hparent : Fits (indexWidth 16 full.length q)
      (state.heap (parentSlot (workspaceBase full.length q) (candidateCount full.length q) node)))
    (hpc : state.pc = 5 * (start + 64)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 361)))
    (count : Nat) (hc : count ≤ candidateCount full.length q) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (innerScanSteps full.length q (order node) count) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (innerScanSteps full.length q (order node) count) state) := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [innerScanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 0 ∧
        RegistersFit (indexWidth 16 full.length q) state from ⟨by intro clock hc; omega, hf⟩)
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
    (tables : InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (node : Nat) (hn : node < nodes)
    (hnode : state.heap (workspaceBase full.length q + 1) = node)
    (hlater : state.heap (workspaceBase full.length q + 2) = 0)
    (hbest : state.heap (workspaceBase full.length q + 3) ≤ q + 1)
    (hparent : Fits (indexWidth 16 full.length q)
      (state.heap (parentSlot (workspaceBase full.length q) (candidateCount full.length q) node)))
    (hpc : state.pc = 5 * (start + 64)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 361))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (innerCompleteSteps full.length q (order node)) ∧
      RegistersFit (indexWidth 16 full.length q)
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
    (RawCandidateOrderingWord.testWorkspace_safe q full 2 (start + 346) (by omega) previous ss.2 pt.base_cell
      (by rw [pt.count_cell]; exact candidateCount_fits _ _)
      (by rw [pj]; exact candidateCount_fits _ _) (lt_of_le_of_lt (by omega) hend))
  dsimp only [chunkLength] at ts
  change PrefixSafe _ _ _ _ (innerScanSteps full.length q (order node) M + 13) ∧
    RegistersFit _ (natRun _ _ (innerScanSteps full.length q (order node) M + 13) _)
  constructor
  · exact PrefixSafe.add _ _ _ _ _ _ ss.1 ts.1
  · rw [natRun_add]
    exact ts.2

theorem outer_iteration_safe (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (node : Nat) (hn : node < nodes)
    (hnode : state.heap (workspaceBase full.length q + 1) = node)
    (hpc : state.pc = 5 * (start + 6)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 361))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (outerIterationSteps full.length q (order node)) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (outerIterationSteps full.length q (order node)) state) := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  have hb : 16 ≤ B := workspaceBase_ge _ _
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
    (RawCandidateParentWordPieces.outerTest_safe q full (start + 361) state hf tables.base_cell tables.count_cell
      (by rw [hnode]; omega) (by rw [nc]; exact ht) hend)
  rw [chunk_run q full containing start hbound hcode .outerTest state hpc ha] at ts
  let prepared := natRun rom containing 37 tested
  have ini := chunk_of_macro q full containing start hbound hcode .initializeChild tested tp ta
    (RawCandidateParentWordPieces.initializeChild_safe q full tested ts.2 tt.base_cell tt.count_cell
      (by rw [th, hnode]; omega))
  have idata := RawCandidateParentRAM.initialize_child q full containing start hbound hcode B nodes order inverse
    tested hb tt node hn (by rw [th]; exact hnode) tp ta
  dsimp only at idata
  obtain ⟨it, ik, ij, ib, ipar, _iframe, pcInit, activeInit⟩ := idata
  have initParent : Fits (indexWidth 16 full.length q) (prepared.heap (parentSlot B M node)) := by
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
  have tm := RawCandidateParentWordPieces.outerTail_safe q full start scanned scan.2 st.base_cell
    (by rw [sk]; omega) hend
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
    (tables : InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse)
    (hnode : state.heap (workspaceBase full.length q + 1) = 0)
    (hpc : state.pc = 5 * (start + 6)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 361)))
    (count : Nat) (hc : count ≤ nodes) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (outerScanSteps full.length q order count) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (outerScanSteps full.length q order count) state) := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [outerScanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 0 ∧
        RegistersFit (indexWidth 16 full.length q) state from ⟨by intro clock hc; omega, hf⟩)
  | succ count ih =>
    intro hc
    obtain ⟨safe, fits⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing (outerScanSteps full.length q order count) state
    have data := RawCandidateParentRAM.outer_scan_partial q full containing start hbound hcode (workspaceBase full.length q)
      nodes order inverse state (workspaceBase_ge _ _) tables hnode hpc ha count (by omega)
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
    (tables : InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 361))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (totalSteps full.length q nodes order) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (totalSteps full.length q nodes order) state) := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  have hb : 16 ≤ B := workspaceBase_ge _ _
  let initialized := runOps rom (RawCandidateOrderingRAM.setWorkspace 1 0) state
  have ini := chunk_of_macro q full containing start hbound hcode .initialize state
    (by simpa only [chunkOffset, Nat.add_zero] using hpc) ha
    (RawCandidateOrderingWord.setWorkspace_safe q full 1 0 (by omega) state hf tables.base_cell (zero_fits _ _))
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
    (RawCandidateParentWordPieces.outerTest_safe q full (start + 361) previous ss.2 pt.base_cell pt.count_cell
      (by rw [pn]; exact ht) (by rw [nc]; exact ht) hend)
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
    (tables : InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 361)))
    (count : Nat) (hc : count ≤ totalSteps full.length q nodes order) :
    let result := natRun (rawIncidenceROM q full) containing count state
    RegistersFit (indexWidth 16 full.length q) result ∧ Fits (indexWidth 16 full.length q) result.pc ∧ result.halted = false := by
  have ss := parents_nat_safe q full containing start hbound hcode nodes order inverse state tables hinverse hpc ha hf hend
  by_cases heq : count = totalSteps full.length q nodes order
  · subst count
    have data := parents_wordData q full containing start hbound hcode nodes order inverse state tables hinverse hpc ha
    exact ⟨ss.2, by rw [data.2.2.1]; exact hend, data.2.2.2⟩
  · have point := ss.1 count (by omega)
    exact ⟨point.1, point.pcFits hend, point.2.choose_spec.2.2.1⟩

theorem word_run_eq_nat (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 361)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ totalSteps full.length q nodes order) :
    packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q)) =
      (natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 16 full.length q) := by
  apply natRun_toWord _ _ _ count hwords
  intro k hk
  have hs := natRun_prefix_safe q full containing start hbound hcode nodes order inverse state tables hinverse hpc ha hf hend k (by omega)
  exact ⟨hs.1, hs.2.1⟩

theorem word_prefix_safe (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 361)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hc : count < totalSteps full.length q nodes order) :
    let after := packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q))
    after.halted = false ∧ after.pc.toNat + 4 < (packingCode containing).length ∧
      ∃ offset < 361, after.pc.toNat = 5 * (start + offset) ∧
        ∃ op, PackingOp.decode (fetch containing after) = some op ∧
          packingAccessFits (rawIncidenceROM q full) (RawCandidateWorkspaceBounds.workspaceLimit full.length q) after op := by
  have hp := (parents_nat_safe q full containing start hbound hcode nodes order inverse state tables hinverse hpc ha hf hend).1 count hc
  have pcFit := hp.pcFits hend
  obtain ⟨offset, hoff, pointer, active, op, decoded, access⟩ := hp.2
  dsimp only
  rw [word_run_eq_nat q full containing start hbound hcode nodes order inverse state tables hinverse hpc ha hf hend hwords count hc.le]
  have pcWord : ((natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 16 full.length q)).pc.toNat =
      5 * (start + offset) := by
    change (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit, pointer]
  refine ⟨active, ?_, offset, hoff, pcWord, op, ?_, ?_⟩
  · rw [pcWord, packingCode_length]
    omega
  · change PackingOp.decode (physicalFetch _ (packingCode containing)
      (BitVec.ofNat _ (natRun (rawIncidenceROM q full) containing count state).pc).toNat) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit, physicalFetch_eq _ _ _ hwords]
    exact decoded
  · exact physical_access_of_nat _ (RawCandidateWorkspaceBounds.workspaceLimit full.length q) _ _ hp.1 access

theorem parents_word (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (tables : InputTables q full (workspaceBase full.length q) nodes order inverse state)
    (hinverse : InverseFits q full inverse) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 361)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing)) :
    let result := natRun (rawIncidenceROM q full) containing (totalSteps full.length q nodes order) state
    packingRun (rawIncidenceROM q full) containing (totalSteps full.length q nodes order)
        (state.toWord (indexWidth 16 full.length q)) = result.toWord (indexWidth 16 full.length q) ∧
      InputTables q full (workspaceBase full.length q) nodes order inverse result ∧
      (∀ node < nodes, Fits (indexWidth 16 full.length q)
        (result.heap (parentSlot (workspaceBase full.length q) (candidateCount full.length q) node))) ∧
      result.pc = 5 * (start + 361) ∧ result.halted = false :=
  ⟨word_run_eq_nat q full containing start hbound hcode nodes order inverse state tables hinverse hpc ha hf hend hwords _ le_rfl,
    parents_wordData q full containing start hbound hcode nodes order inverse state tables hinverse hpc ha⟩

/-- The actual completed sorting result discharges all source-word bounds
for the parent stage.  No inverse or parent answer is an added premise. -/
theorem parents_of_sorted_nat_safe (sortStart : Nat) (before state : NatState)
    (sorted : RawCandidateOrderingRAM.Sorted q full (workspaceBase full.length q) sortStart before state)
    (hq : 0 < q) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 361))) :
    let nodes := (RawCandidateOrder.retainedCandidateIndices q full).length
    let order := observedOrder q full (workspaceBase full.length q) state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (totalSteps full.length q nodes order) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (totalSteps full.length q nodes order) state) :=
  parents_nat_safe q full containing start hbound hcode _ _ _ state
    (InputTables.of_sorted q full _ sortStart before state sorted hq)
    (inverseFits_of_sorted q full sortStart before state sorted) hpc ha hf hend

theorem parents_of_sorted_word (sortStart : Nat) (before state : NatState)
    (sorted : RawCandidateOrderingRAM.Sorted q full (workspaceBase full.length q) sortStart before state)
    (hq : 0 < q) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 361)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing)) :
    let nodes := (RawCandidateOrder.retainedCandidateIndices q full).length
    let order := observedOrder q full (workspaceBase full.length q) state
    let inverse := observedInverse q full (workspaceBase full.length q) state
    let result := natRun (rawIncidenceROM q full) containing (totalSteps full.length q nodes order) state
    packingRun (rawIncidenceROM q full) containing (totalSteps full.length q nodes order)
        (state.toWord (indexWidth 16 full.length q)) = result.toWord (indexWidth 16 full.length q) ∧
      InputTables q full (workspaceBase full.length q) nodes order inverse result ∧
      (∀ node < nodes, Fits (indexWidth 16 full.length q)
        (result.heap (parentSlot (workspaceBase full.length q) (candidateCount full.length q) node))) ∧
      result.pc = 5 * (start + 361) ∧ result.halted = false :=
  parents_word q full containing start hbound hcode _ _ _ state
    (InputTables.of_sorted q full _ sortStart before state sorted hq)
    (inverseFits_of_sorted q full sortStart before state sorted) hpc ha hf hend hwords

end Linked

end PaperProofs.Structure.LaminarTree.RawCandidateParentWord
