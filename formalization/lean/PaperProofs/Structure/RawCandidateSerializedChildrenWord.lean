module

public import PaperProofs.Structure.RawCandidateSerializedChildrenRun
public import PaperProofs.Structure.RawCandidateOrderingWord
public import PaperProofs.Structure.RawCandidateSerializedChildrenWordChunks
public import PaperProofs.Structure.RawCandidateSerializedInputWordPieces
public import PaperProofs.Structure.RawCandidateSerializedChildrenWordPieces

/-! Actual child-serializer loop safety. The initial input predicate is the
preceding machine's real header/parent cache; partial written regions occur
only as conclusions of existing actual loop semantics. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedChildrenWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawTreeSerialization
open RawCandidateWorkspaceInit (workspaceBase candidateCount workspaceBase_ge)
open RawCandidateSerializedChildrenRAM RawCandidateSerializedChildrenRun
open RawCandidateSerializedChildrenWordChunks (Chunk chunkCode chunkOffset chunkLength SafePoint chunk_run chunk_of_macro)

theorem size_le (q : Nat) (full : List (Finset (Fin q))) : size q full ≤ candidateCount full.length q :=
  prepared_indexed_size_le q full

theorem parentWords_bound (q : Nat) (full : List (Finset (Fin q))) (child : Nat) (hc : child < size q full) :
    parentWords q full child ≤ candidateCount full.length q := by
  rw [RawCandidateSerializedChildrenRAM.parentWords, RawCandidateChildrenLayout.givenTreeROM_parentWords q full child hc]
  exact (UniformNormalizationRAM.encodedNode_le _ _).trans (size_le q full)

theorem input_parent_bound (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (input : RawCandidateSerializedChildrenRAM.InputSpec q full state) (child : Nat) (hc : child < size q full) :
    state.heap (parentAddress full.length q child) ≤ candidateCount full.length q := by
  rw [input.parents child hc]
  exact parentWords_bound q full child hc

theorem input_header_bounds (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (state : NatState) (input : RawCandidateSerializedChildrenRAM.InputSpec q full state) :
    state.heap 0 ≤ workspaceBase full.length q ∧
      state.heap 1 ≤ 2 * candidateCount full.length q ∧ state.heap 5 ≤ candidateCount full.length q := by
  have he := endAddress_lt_base q full hq hl
  have hs : 3 + (givenTreeROM q full).input.length ≤ endAddress q full := by
    unfold endAddress childrenStart internalStart
    omega
  rw [input.header0, input.header1, input.header5]
  have ht := size_le q full
  exact ⟨by omega, by omega, ht⟩

theorem beforeList_bound (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (node : Nat) (hn : node ≤ size q full) :
    (beforeList q full node).length ≤ candidateCount full.length q := by
  have h := RawCandidateChildrenPrefix.flatPrefix_length_mono (size q full) (parentWords q full) node (size q full) hn
  change (beforeList q full node).length ≤ (beforeList q full (size q full)).length at h
  rw [beforeList_full, givenTreeROM_children_length q full hq hl] at h
  exact h.trans ((Nat.sub_le _ _).trans (size_le q full))

theorem rowList_bound (q : Nat) (full : List (Finset (Fin q))) (node child : Nat) (hc : child ≤ size q full) :
    (rowList q full node child).length ≤ candidateCount full.length q :=
  (RawCandidateChildrenPrefix.childPrefix_length_le_upto (size q full) (parentWords q full) node child).trans
    (hc.trans (size_le q full))

theorem scanList_bound (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (node child : Nat) (hn : node < size q full) (hc : child ≤ size q full) :
    (scanList q full node child).length ≤ candidateCount full.length q := by
  have h := scanList_length_le q full node child hn hc
  rw [givenTreeROM_children_length q full hq hl] at h
  exact h.trans ((Nat.sub_le _ _).trans (size_le q full))

theorem outer_ready_bounds (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (node pointer : Nat) (state : NatState)
    (ready : OuterReady q full node pointer state) (hn : node ≤ size q full) :
    state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q ∧
      state.heap (flatAddress full.length q) ≤ candidateCount full.length q := by
  rw [ready.node_cell, ready.flat_cell]
  exact ⟨hn.trans (size_le q full), beforeList_bound q full hq hl node hn⟩

theorem inner_ready_bounds (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (node child pointer : Nat) (state : NatState)
    (ready : InnerReady q full node child pointer state) (hn : node < size q full) (hc : child ≤ size q full) :
    state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q ∧
      state.heap (workspaceBase full.length q + 2) ≤ candidateCount full.length q ∧
      state.heap (workspaceBase full.length q + 3) ≤ candidateCount full.length q ∧
      state.heap (flatAddress full.length q) ≤ candidateCount full.length q := by
  rw [ready.cursor.node_cell, ready.cursor.child_cell, ready.degree_cell, ready.flat_cell]
  exact ⟨hn.le.trans (size_le q full), hc.trans (size_le q full), rowList_bound q full node child hc,
    scanList_bound q full hq hl node child hn hc⟩

theorem bounded_word (N q value : Nat) (hv : value ≤ candidateCount N q + 1) : Fits (indexWidth 16 N q) value := by
  apply RawCandidateWorkspaceBounds.workspace_address_fits
  unfold RawCandidateWorkspaceBounds.workspaceLimit
  omega

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
  (containing : List PackingOp) (start : Nat)
  (hbound : start + 427 ≤ containing.length)
  (hcode : ∀ position < 427, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hq hl hbound hcode

theorem child_scan_word_bounds (node : Nat) (state : NatState)
    (ready : InnerReady q full node 0 (5 * (start + 127)) state) (hn : node < size q full)
    (count : Nat) (hc : count ≤ size q full) :
    let result := natRun (rawIncidenceROM q full) containing (childSteps q full node count) state
    result.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q ∧
      result.heap (workspaceBase full.length q + 2) ≤ candidateCount full.length q ∧
      result.heap (workspaceBase full.length q + 3) ≤ candidateCount full.length q ∧
      result.heap (flatAddress full.length q) ≤ candidateCount full.length q := by
  have hs := RawCandidateSerializedChildrenRun.child_scan_partial q full hq hl containing start hbound hcode
    node state ready hn count hc
  exact inner_ready_bounds q full hq hl node count _ _ hs.1 hn hc

theorem outer_scan_word_bounds (state : NatState)
    (ready : OuterReady q full 0 (5 * (start + 35)) state) (count : Nat) (hc : count ≤ size q full) :
    let result := natRun (rawIncidenceROM q full) containing (outerSteps q full count) state
    result.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q ∧
      result.heap (flatAddress full.length q) ≤ candidateCount full.length q := by
  have hs := RawCandidateSerializedChildrenRun.outer_scan_partial q full hq hl containing start hbound hcode
    state ready count hc
  exact outer_ready_bounds q full hq hl count _ _ hs.1 hc

theorem child_iteration_safe (node child : Nat) (state : NatState)
    (ready : InnerReady q full node child (5 * (start + 127)) state)
    (hn : node < size q full) (hc : child < size q full)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (bitSteps (RawCandidateSerializedChildrenRAM.parentWords q full) node child) ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing
        (bitSteps (RawCandidateSerializedChildrenRAM.parentWords q full) node child) state) := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  have hb : 16 ≤ B := workspaceBase_ge _ _
  have bounds := inner_ready_bounds q full hq hl node child _ state ready hn hc.le
  have headers := input_header_bounds q full hq hl state ready.cursor.input
  have ht := RawCandidateSerializedInputWordPieces.boundedTest_safe q full 2 5 (start + 353) (by omega) (by omega)
    state hf (bounded_word _ _ _ (bounds.2.1.trans (Nat.le_succ _)))
    (bounded_word _ _ _ (headers.2.2.trans (Nat.le_succ _))) (lt_of_le_of_lt (by omega) hend)
  have ts := chunk_of_macro q full containing start hbound hcode .innerTest state ready.cursor.pc ready.cursor.active ht
  let tested := runOps rom (RawCandidateSerializedInputRAM.boundedTest 2 5 (start + 353)) state
  have tv := RawCandidateSerializedInputRAM.boundedTest_values q full 2 5 (start + 353) state
  have th : tested.heap = state.heap := tv.1
  have tp : tested.pc = 5 * (start + 147) := by
    have hp := tv.2.1
    rw [ready.cursor.input.header5, ready.cursor.child_cell, ite_eq_right (Nat.sub_ne_zero_of_lt hc), ready.cursor.pc] at hp
    dsimp only [tested]
    omega
  have ta : tested.halted = false := tv.2.2.trans ready.cursor.active
  have runT : natRun rom containing 20 state = tested := by
    exact chunk_run q full containing start hbound hcode .innerTest state ready.cursor.pc ready.cursor.active
  have pm : tested.heap (parentAddress full.length q (tested.heap (B + 2))) ≤ M := by
    rw [th, ready.cursor.child_cell]
    exact input_parent_bound q full state ready.cursor.input child hc
  have mt := RawCandidateSerializedChildrenWordPieces.matchTest_safe q full start tested ht.full
    (by rw [th]; exact bounds.1) (by rw [th]; exact bounds.2.1) pm hend
  have ms := chunk_of_macro q full containing start hbound hcode .matchTest tested tp ta mt
  let checked := runOps rom (matchTest start) tested
  have mv := matchTest_values q full start tested
  have ch : checked.heap = state.heap := mv.1.trans th
  have ca : checked.halted = false := mv.2.1.trans ta
  have cp : checked.pc = if RawCandidateSerializedChildrenRAM.parentWords q full child = node + 1 then
      5 * (start + 206) else 5 * (start + 203) := by
    calc
      checked.pc = if tested.heap (parentAddress full.length q (tested.heap (B + 2))) =
          tested.heap (B + 1) + 1 then 5 * (start + 206) else tested.pc + 280 := mv.2.2
      _ = _ := by
        rw [th, ready.cursor.child_cell, ready.cursor.node_cell, ready.cursor.input.parents child hc, tp]
        split <;> omega
  have runM : natRun rom containing 56 tested = checked := chunk_run q full containing start hbound hcode .matchTest tested tp ta
  dsimp only [chunkLength] at ts ms
  by_cases heq : RawCandidateSerializedChildrenRAM.parentWords q full child = node + 1
  · have mpc : checked.pc = 5 * (start + 206) := by simpa only [ite_eq_left heq] using cp
    have mm := RawCandidateSerializedChildrenWordPieces.matched_safe q full checked mt.full
      (by rw [ch]; exact bounds.2.1) (by rw [ch]; exact bounds.2.2.1) (by rw [ch]; exact bounds.2.2.2)
      (by rw [ch]; exact headers.1) (by rw [ch]; exact headers.2.1)
    have ws := chunk_of_macro q full containing start hbound hcode .matched checked mpc ca mm
    let written := runOps rom matched checked
    have target : 3 + checked.heap 0 + checked.heap 1 + checked.heap (flatAddress full.length q) < B := by
      rw [ch, ready.cursor.input.header0, ready.cursor.input.header1, ready.flat_cell]
      exact (matched_position_lt q full node child hn hc heq).trans (endAddress_lt_base q full hq hl)
    have wh := matched_heap q full checked target
    have wc : written.heap (B + 2) ≤ M := by
      change (runOps rom matched checked).heap (B + 2) ≤ M
      rw [wh, ch]
      have targetState : 3 + state.heap 0 + state.heap 1 + state.heap (flatAddress full.length q) < B := by
        simpa only [ch] using target
      rw [Function.update_of_ne (by dsimp only [B]; unfold flatAddress; omega),
        Function.update_of_ne (by dsimp only [B]; omega), Function.update_of_ne (by omega)]
      exact bounds.2.1
    have wp : written.pc = 5 * (start + 318) := by
      rw [show written = runOps rom matched checked from rfl, runOps_pc _ _ _ (by
        dsimp [matched, writeChild, RawCandidateSerializedInputRAM.loadCache, loadFlat,
          RawCandidateSerializedInputRAM.incrementCache, incrementFlat, storeFlat,
          RawCandidateSerializedInputRAM.storeCache, RawCandidateWorkspaceBaseRAM.program, loadCell, NoJump]
        simp), matched_length, mpc]
      omega
    have wa : written.halted = false := (runOps_halted _ _ _).trans ca
    have tail := RawCandidateSerializedChildrenWordPieces.innerTail_safe q full start written mm.full wc hend
    have fs := chunk_of_macro q full containing start hbound hcode .innerTail written wp wa tail
    have runW : natRun rom containing 112 checked = written := chunk_run q full containing start hbound hcode .matched checked mpc ca
    have runF : natRun rom containing 35 written = runOps rom (innerTail start) written :=
      chunk_run q full containing start hbound hcode .innerTail written wp wa
    dsimp only [chunkLength] at ws fs
    have rest : PrefixSafe (SafePoint q full containing start) rom containing checked (112 + 35) := by
      apply PrefixSafe.add _ _ _ _ 112 35 ws.1
      rw [runW]
      exact fs.1
    have afterTest : PrefixSafe (SafePoint q full containing start) rom containing tested (56 + (112 + 35)) := by
      apply PrefixSafe.add _ _ _ _ 56 _ ms.1
      rw [runM]
      exact rest
    rw [bitSteps, ite_eq_left heq, show 223 = 20 + (56 + (112 + 35)) by decide]
    constructor
    · apply PrefixSafe.add _ _ _ _ 20 _ ts.1
      rw [runT]
      exact afterTest
    · rw [natRun_add, runT, natRun_add, runM, natRun_add, runW, runF]
      exact tail.full
  · have mpc : checked.pc = 5 * (start + 203) := by simpa only [ite_eq_right heq] using cp
    have skip := RawCandidateOrderingWord.jump_safe q full (start + 318) checked mt.full (lt_of_le_of_lt (by omega) hend)
    have ss := chunk_of_macro q full containing start hbound hcode .skipMatch checked mpc ca skip
    let skipped := runOps rom (jumpTo (start + 318)) checked
    have sh : skipped.heap = state.heap := (show skipped.heap = checked.heap from rfl).trans ch
    have sp : skipped.pc = 5 * (start + 318) := by
      simp [skipped, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
    have sa : skipped.halted = false := (runOps_halted _ _ _).trans ca
    have sc : skipped.heap (B + 2) ≤ M := by rw [sh]; exact bounds.2.1
    have tail := RawCandidateSerializedChildrenWordPieces.innerTail_safe q full start skipped skip.full sc hend
    have fs := chunk_of_macro q full containing start hbound hcode .innerTail skipped sp sa tail
    have runS : natRun rom containing 3 checked = skipped := chunk_run q full containing start hbound hcode .skipMatch checked mpc ca
    have runF : natRun rom containing 35 skipped = runOps rom (innerTail start) skipped :=
      chunk_run q full containing start hbound hcode .innerTail skipped sp sa
    dsimp only [chunkLength] at ss fs
    have rest : PrefixSafe (SafePoint q full containing start) rom containing checked (3 + 35) := by
      apply PrefixSafe.add _ _ _ _ 3 35 ss.1
      rw [runS]
      exact fs.1
    have afterTest : PrefixSafe (SafePoint q full containing start) rom containing tested (56 + (3 + 35)) := by
      apply PrefixSafe.add _ _ _ _ 56 _ ms.1
      rw [runM]
      exact rest
    rw [bitSteps, ite_eq_right heq, show 114 = 20 + (56 + (3 + 35)) by decide]
    constructor
    · apply PrefixSafe.add _ _ _ _ 20 _ ts.1
      rw [runT]
      exact afterTest
    · rw [natRun_add, runT, natRun_add, runM, natRun_add, runS, runF]
      exact tail.full

theorem row_initialize_safe (node : Nat) (state : NatState)
    (ready : OuterReady q full node (5 * (start + 35)) state) (hn : node < size q full)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 92 ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing 92 state) := by
  let rom := rawIncidenceROM q full
  have bounds := outer_ready_bounds q full hq hl node _ state ready hn.le
  have headers := input_header_bounds q full hq hl state ready.input
  have t := RawCandidateSerializedInputWordPieces.boundedTest_safe q full 1 5 (start + 427) (by omega) (by omega)
    state hf (bounded_word _ _ _ (bounds.1.trans (Nat.le_succ _)))
    (bounded_word _ _ _ (headers.2.2.trans (Nat.le_succ _))) hend
  have ts := chunk_of_macro q full containing start hbound hcode .outerTest state ready.pc ready.active t
  let tested := runOps rom (RawCandidateSerializedInputRAM.boundedTest 1 5 (start + 427)) state
  have tv := RawCandidateSerializedInputRAM.boundedTest_values q full 1 5 (start + 427) state
  have th : tested.heap = state.heap := tv.1
  have tp : tested.pc = 5 * (start + 55) := by
    have hp := tv.2.1
    rw [ready.input.header5, ready.node_cell, ite_eq_right (Nat.sub_ne_zero_of_lt hn), ready.pc] at hp
    dsimp only [tested]
    omega
  have ta : tested.halted = false := tv.2.2.trans ready.active
  have parent : Fits (indexWidth 16 full.length q)
      (tested.heap (parentAddress full.length q (tested.heap (workspaceBase full.length q + 1)))) := by
    rw [th, ready.node_cell]
    exact bounded_word _ _ _ ((input_parent_bound q full state ready.input node hn).trans (Nat.le_succ _))
  have m := RawCandidateSerializedChildrenWordPieces.initRow_safe q full tested t.full
    (by rw [th]; exact bounds.1) (by rw [th]; exact headers.1) parent
  have ms := chunk_of_macro q full containing start hbound hcode .initRow tested tp ta m
  have runT : natRun rom containing 20 state = tested := chunk_run q full containing start hbound hcode .outerTest state ready.pc ready.active
  have runM : natRun rom containing 72 tested = runOps rom initRow tested := chunk_run q full containing start hbound hcode .initRow tested tp ta
  dsimp only [chunkLength] at ts ms
  constructor
  · change PrefixSafe _ _ _ _ (20 + 72)
    apply PrefixSafe.add _ _ _ _ 20 72 ts.1
    rw [runT]
    exact ms.1
  · rw [show 92 = 20 + 72 by decide, natRun_add, runT, runM]
    exact m.full

theorem child_scan_partial_safe (node : Nat) (state : NatState)
    (ready : InnerReady q full node 0 (5 * (start + 127)) state) (hn : node < size q full)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427))) (count : Nat) (hc : count ≤ size q full) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (childSteps q full node count) ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing (childSteps q full node count) state) := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [childSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 0 ∧
        RegistersFit (indexWidth 16 full.length q) state from ⟨fun _ hc => by omega, hf⟩)
  | succ count ih =>
    intro hc
    have previousSafe := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing (childSteps q full node count) state
    have rn := RawCandidateSerializedChildrenRun.child_scan_partial q full hq hl containing start hbound hcode
      node state ready hn count (by omega)
    have step := child_iteration_safe q full hq hl containing start hbound hcode node count previous rn.1 hn
      (by omega) previousSafe.2 hend
    rw [childSteps_succ]
    exact ⟨PrefixSafe.add _ _ _ _ _ _ previousSafe.1 step.1, by rw [natRun_add]; exact step.2⟩

theorem child_scan_safe (node : Nat) (state : NatState)
    (ready : InnerReady q full node 0 (5 * (start + 127)) state) (hn : node < size q full)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (childSteps q full node (size q full) + 20) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (childSteps q full node (size q full) + 20) state) := by
  let rom := rawIncidenceROM q full
  let previous := natRun rom containing (childSteps q full node (size q full)) state
  have scan := child_scan_partial_safe q full hq hl containing start hbound hcode node state ready hn hf hend (size q full) le_rfl
  have rn := RawCandidateSerializedChildrenRun.child_scan_partial q full hq hl containing start hbound hcode
    node state ready hn (size q full) le_rfl
  have bounds := inner_ready_bounds q full hq hl node (size q full) _ previous rn.1 hn le_rfl
  have headers := input_header_bounds q full hq hl previous rn.1.cursor.input
  have t := RawCandidateSerializedInputWordPieces.boundedTest_safe q full 2 5 (start + 353) (by omega) (by omega)
    previous scan.2 (bounded_word _ _ _ (bounds.2.1.trans (Nat.le_succ _)))
    (bounded_word _ _ _ (headers.2.2.trans (Nat.le_succ _))) (lt_of_le_of_lt (by omega) hend)
  have ts := chunk_of_macro q full containing start hbound hcode .innerTest previous rn.1.cursor.pc rn.1.cursor.active t
  dsimp only [chunkLength] at ts
  exact ⟨PrefixSafe.add _ _ _ _ _ 20 scan.1 ts.1, by rw [natRun_add]; exact ts.2⟩

theorem row_finish_safe (node : Nat) (state : NatState)
    (ready : InnerReady q full node (size q full) (5 * (start + 353)) state) (hn : node < size q full)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 74 ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing 74 state) := by
  have bounds := inner_ready_bounds q full hq hl node (size q full) _ state ready hn le_rfl
  have headers := input_header_bounds q full hq hl state ready.cursor.input
  have m := RawCandidateSerializedChildrenWordPieces.outerTail_safe q full start state hf
    bounds.1 bounds.2.2.1 headers.1 headers.2.2 hend
  exact chunk_of_macro q full containing start hbound hcode .outerTail state ready.cursor.pc ready.cursor.active m

theorem row_iteration_safe (node : Nat) (state : NatState)
    (ready : OuterReady q full node (5 * (start + 35)) state) (hn : node < size q full)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (rowSteps q full node) ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing (rowSteps q full node) state) := by
  let rom := rawIncidenceROM q full
  let initialized := natRun rom containing 92 state
  have init := row_initialize_safe q full hq hl containing start hbound hcode node state ready hn hf hend
  have ri := RawCandidateSerializedChildrenRun.row_initialize q full hq hl containing start hbound hcode node state ready hn
  let scanned := natRun rom containing (childSteps q full node (size q full) + 20) initialized
  have scan := child_scan_safe q full hq hl containing start hbound hcode node initialized ri.1 hn init.2 hend
  have rs := RawCandidateSerializedChildrenRun.child_scan q full hq hl containing start hbound hcode node initialized ri.1 hn
  have finish := row_finish_safe q full hq hl containing start hbound hcode node scanned rs.1 hn scan.2 hend
  rw [show rowSteps q full node = 92 + ((childSteps q full node (size q full) + 20) + 74) by unfold rowSteps; omega]
  constructor
  · apply PrefixSafe.add _ _ _ _ 92 _ init.1
    exact PrefixSafe.add _ _ _ _ _ 74 scan.1 finish.1
  · rw [natRun_add, natRun_add]
    exact finish.2

theorem outer_scan_partial_safe (state : NatState)
    (ready : OuterReady q full 0 (5 * (start + 35)) state)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427))) (count : Nat) (hc : count ≤ size q full) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (outerSteps q full count) ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing (outerSteps q full count) state) := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [outerSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 0 ∧
        RegistersFit (indexWidth 16 full.length q) state from ⟨fun _ hc => by omega, hf⟩)
  | succ count ih =>
    intro hc
    have ps := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing (outerSteps q full count) state
    have rp := RawCandidateSerializedChildrenRun.outer_scan_partial q full hq hl containing start hbound hcode state ready count (by omega)
    have step := row_iteration_safe q full hq hl containing start hbound hcode count previous rp.1 (by omega) ps.2 hend
    rw [outerSteps_succ]
    exact ⟨PrefixSafe.add _ _ _ _ _ _ ps.1 step.1, by rw [natRun_add]; exact step.2⟩

theorem serialize_nat_safe (state : NatState)
    (input : RawCandidateSerializedChildrenRAM.InputSpec q full state)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (totalSteps q full) ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing (totalSteps q full) state) := by
  let rom := rawIncidenceROM q full
  have m := RawCandidateSerializedChildrenWordPieces.initBlock_safe q full state hf
  have ini := chunk_of_macro q full containing start hbound hcode .initBlock state
    (by simpa only [chunkOffset, Nat.add_zero] using hpc) ha m
  let initialized := natRun rom containing 35 state
  have ri := RawCandidateSerializedChildrenRun.initialize_phase q full hq hl containing start hbound hcode state input hpc ha
  dsimp only [chunkLength] at ini
  have scan := outer_scan_partial_safe q full hq hl containing start hbound hcode initialized ri.1 ini.2 hend (size q full) le_rfl
  let previous := natRun rom containing (outerSteps q full (size q full)) initialized
  have rp := RawCandidateSerializedChildrenRun.outer_scan_partial q full hq hl containing start hbound hcode initialized ri.1 (size q full) le_rfl
  have bounds := outer_ready_bounds q full hq hl (size q full) _ previous rp.1 le_rfl
  have headers := input_header_bounds q full hq hl previous rp.1.input
  have t := RawCandidateSerializedInputWordPieces.boundedTest_safe q full 1 5 (start + 427) (by omega) (by omega)
    previous scan.2 (bounded_word _ _ _ (bounds.1.trans (Nat.le_succ _)))
    (bounded_word _ _ _ (headers.2.2.trans (Nat.le_succ _))) hend
  have ts := chunk_of_macro q full containing start hbound hcode .outerTest previous rp.1.pc rp.1.active t
  dsimp only [chunkLength] at ts
  rw [totalSteps, Nat.add_assoc]
  constructor
  · apply PrefixSafe.add _ _ _ _ 35 _ ini.1
    exact PrefixSafe.add _ _ _ _ _ 20 scan.1 ts.1
  · rw [natRun_add, natRun_add]
    exact ts.2

theorem natRun_prefix_safe (state : NatState)
    (input : RawCandidateSerializedChildrenRAM.InputSpec q full state)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427))) (count : Nat) (hc : count ≤ totalSteps q full) :
    RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing count state) ∧
      Fits (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing count state).pc ∧
      (natRun (rawIncidenceROM q full) containing count state).halted = false := by
  have hs := serialize_nat_safe q full hq hl containing start hbound hcode state input hpc ha hf hend
  by_cases hlt : count < totalSteps q full
  · have hp := hs.1 count hlt
    have pcFit := hp.pcFits hend
    obtain ⟨offset, hoff, pc, active, op, hd, hx⟩ := hp.2
    exact ⟨hp.1, pcFit, active⟩
  · have heq : count = totalSteps q full := by omega
    subst count
    have sem := RawCandidateSerializedChildrenRun.serialize_phase q full hq hl containing start hbound hcode state input hpc ha
    exact ⟨hs.2, by rw [sem.1.pc]; exact hend, sem.1.active⟩

theorem word_run_eq_nat (state : NatState)
    (input : RawCandidateSerializedChildrenRAM.InputSpec q full state)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ totalSteps q full) :
    packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q)) =
      (natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 16 full.length q) := by
  apply natRun_toWord _ _ _ count hwords
  intro clock hclock
  have hs := natRun_prefix_safe q full hq hl containing start hbound hcode state input hpc ha hf hend clock (by omega)
  exact ⟨hs.1, hs.2.1⟩

theorem word_prefix_safe (state : NatState)
    (input : RawCandidateSerializedChildrenRAM.InputSpec q full state)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hc : count < totalSteps q full) :
    let after := packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q))
    after.halted = false ∧ after.pc.toNat + 4 < (packingCode containing).length ∧
      ∃ offset < 427, after.pc.toNat = 5 * (start + offset) ∧
        ∃ op, PackingOp.decode (fetch containing after) = some op ∧
          packingAccessFits (rawIncidenceROM q full) (RawCandidateWorkspaceBounds.workspaceLimit full.length q) after op := by
  have hp := (serialize_nat_safe q full hq hl containing start hbound hcode state input hpc ha hf hend).1 count hc
  have pcFit := hp.pcFits hend
  obtain ⟨offset, hoff, pointer, active, op, decoded, access⟩ := hp.2
  dsimp only
  rw [word_run_eq_nat q full hq hl containing start hbound hcode state input hpc ha hf hend hwords count hc.le]
  have hpcWord : ((natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 16 full.length q)).pc.toNat =
      5 * (start + offset) := by
    change (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit, pointer]
  refine ⟨active, ?_, offset, hoff, hpcWord, op, ?_, ?_⟩
  · rw [hpcWord, packingCode_length]
    omega
  · change PackingOp.decode (physicalFetch _ (packingCode containing)
      (BitVec.ofNat _ (natRun (rawIncidenceROM q full) containing count state).pc).toNat) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit, physicalFetch_eq _ _ _ hwords]
    exact decoded
  · exact physical_access_of_nat _ (RawCandidateWorkspaceBounds.workspaceLimit full.length q) _ _ hp.1 access

theorem serialize_word (state : NatState)
    (input : RawCandidateSerializedChildrenRAM.InputSpec q full state)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing)) :
    let result := natRun (rawIncidenceROM q full) containing (totalSteps q full) state
    packingRun (rawIncidenceROM q full) containing (totalSteps q full) (state.toWord (indexWidth 16 full.length q)) =
        result.toWord (indexWidth 16 full.length q) ∧
      Output q full (5 * (start + 427)) state result :=
  ⟨word_run_eq_nat q full hq hl containing start hbound hcode state input hpc ha hf hend hwords _ le_rfl,
    RawCandidateSerializedChildrenRun.serialize q full hq hl containing start hbound hcode state input hpc ha⟩

end Linked

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedChildrenWord
