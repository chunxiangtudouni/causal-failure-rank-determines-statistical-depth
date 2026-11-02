module

public import Structure.PA06_A19Prepare_CompactOrdering034Data
public import Structure.PA06_A19Prepare_ROM_001

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Actual original303-op sort-loop safety. Generic Nat rank scans, stable
ordering semantics, code slices and true chunk runs are reused directly.
Only the real macro/source qualifications from034/018/014 compose into
full width32 and008 linearLimit. No sorted answer or all-run safety is a
caller premise; the ordinary input tables come from real retention. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactOrdering034Loop

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateOrderingRAM RawIncidenceScanSafety
open PA06A19PrepareCompactOrdering034Macros PA06A19PrepareCompactOrdering034Data
open RawCandidateOrderingWord (Chunk chunkCode chunkOffset chunkLength chunkLead
  chunkLast chunk_code_length chunk_span chunk_lead_length chunk_lead_noJump
  chunk_slice chunk_run_prefix chunk_run)

private theorem count_fits (N q : Nat) : Fits (indexWidth 32 N q) (N + q + 1) :=
  PA06A19PrepareCompactArrays018.value_le_count_fits N q _ le_rfl

def SafePoint (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat) (state : NatState) : Prop :=
  RegistersFit (indexWidth 32 full.length q) state ∧
    ∃ offset < 303, state.pc = 5 * (start + offset) ∧ state.halted = false ∧
      ∃ op, PackingOp.decode (natFetch containing state.pc) = some op ∧
        NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q) state op

theorem SafePoint.pcFits {q : Nat} {full : List (Finset (Fin q))} {containing : List PackingOp} {start : Nat}
    {state : NatState} (h : SafePoint q full containing start state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 303))) :
    Fits (indexWidth 32 full.length q) state.pc := by
  obtain ⟨offset, hoff, hp, _⟩ := h.2
  rw [hp]
  exact lt_of_le_of_lt (by omega) hend


section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 303 ≤ containing.length)
  (hcode : ∀ position < 303, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem outer_iteration_ordFits (index : Nat) (state : NatState)
    (ready : OuterReady 16 (full.length + q + 1) index (5 * (start + 9)) state)
    (htables : InputTables 16 (full.length + q + 1)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hi : index < (full.length + q + 1)) (hord : OrdFits q full state) :
    OrdFits q full (natRun (rawIncidenceROM q full) containing
      (138 * (full.length + q + 1) + 154) state) := by
  let B := 16
  let M := (full.length + q + 1)
  let rank := rankCount (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) index M
  have hb : 16 ≤ B := (show 16 ≤ 16 from le_rfl)
  have hrank : rank < M := rankCount_lt _ _ _ _ hi
  have hn := RawCandidateOrderingRAM.outer_iteration (rawIncidenceROM q full) containing start hbound hcode B M index
    (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state hb ready htables hi
  dsimp only at hn
  obtain ⟨_rn, _tables, _count, _inverse, order, frame⟩ := hn
  intro position hp
  by_cases heq : position = rank
  · subst position
    rw [order]
    split
    · exact scalar_fits _ _ _ (by omega)
    · exact hord rank hrank
  · rw [frame (arraySlot B M 2 position)
      (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
      (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
      (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
      (by unfold arraySlot; omega) (by intro _; unfold arraySlot; omega)]
    exact hord position hp

theorem outer_scan_partial_ordFits (state : NatState)
    (ready : OuterReady 16 (full.length + q + 1) 0 (5 * (start + 9)) state)
    (htables : InputTables 16 (full.length + q + 1)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hzero : state.heap 0 = 0) (hord : OrdFits q full state)
    (upto : Nat) (hupto : upto ≤ (full.length + q + 1)) :
    OrdFits q full (natRun (rawIncidenceROM q full) containing
      ((138 * (full.length + q + 1) + 154) * upto) state) := by
  revert hupto
  induction upto with
  | zero => intro _; exact hord
  | succ upto ih =>
    intro hupto
    have prior := ih (by omega)
    have pn := RawCandidateOrderingRAM.outer_scan_partial (rawIncidenceROM q full) containing start hbound hcode q full
      16 state ((show 16 ≤ 16 from le_rfl)) ready htables hzero upto ((Nat.le_succ upto).trans hupto)
    dsimp only at pn
    rw [Nat.mul_succ, natRun_add]
    exact outer_iteration_ordFits q full containing start hbound hcode upto _ pn.1 pn.2.1 (by omega) prior

theorem chunk_safe (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (hf : ∀ count ≤ chunkLength chunk, RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state))
    (hx : ∀ count < chunkLength chunk, NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state)
      ((chunkCode start chunk).getD count paddingOp)) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (chunkLength chunk) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength chunk) state) := by
  constructor
  · intro count hc
    have hr := chunk_run_prefix q full containing start hbound hcode chunk state hpc ha count hc.le
    have hsmall : count ≤ chunkLength chunk - 1 := by omega
    have heq : (chunkCode start chunk).take count = (chunkLead start chunk).take count := by
      rw [chunkLead, List.take_take, min_eq_left hsmall]
    have hno : ∀ op ∈ (chunkCode start chunk).take count, NoJump op := by
      rw [heq]
      exact fun op hop => chunk_lead_noJump start chunk op (List.mem_of_mem_take hop)
    have hp : (natRun (rawIncidenceROM q full) containing count state).pc =
        5 * (start + chunkOffset chunk + count) := by
      rw [hr, runOps_pc _ _ _ hno,
        List.length_take_of_le (by rw [chunk_code_length]; omega), hpc]
      omega
    have hs := chunk_span chunk
    refine ⟨?_, chunkOffset chunk + count, by omega, ?_, ?_,
      (chunkCode start chunk).getD count paddingOp, ?_, ?_⟩
    · rw [hr]
      exact hf count hc.le
    · rw [hp]
      omega
    · rw [hr, runOps_halted, ha]
    · rw [hp, natFetch_body containing (start + chunkOffset chunk + count) (by omega), decode_encode]
      have hh := (hcode (chunkOffset chunk + count) (by omega)).trans (chunk_slice start chunk count hc)
      rw [List.getD_eq_getElem _ paddingOp (by omega)] at hh
      simpa only [Nat.add_assoc] using congrArg some hh
    · rw [hr]
      exact hx count hc
  · rw [chunk_run q full containing start hbound hcode chunk state hpc ha]
    have hh := hf _ le_rfl
    rwa [List.take_of_length_le (by rw [chunk_code_length])] at hh

theorem chunk_of_macro (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (hm : MacroSafe q full (chunkCode start chunk) state) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (chunkLength chunk) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength chunk) state) := by
  apply chunk_safe q full containing start hbound hcode chunk state hpc ha
  · intro count hc
    exact hm.1 count (by rw [chunk_code_length]; exact hc)
  · intro count hc
    exact hm.2 count (by rw [chunk_code_length]; exact hc)

theorem inner_iteration_safe (left right rank : Nat) (state : NatState)
    (ready : RankReady 16 (full.length + q + 1) left right rank
      (5 * (start + 34)) state)
    (htables : InputTables 16 (full.length + q + 1)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hl : left < (full.length + q + 1)) (hr : right < (full.length + q + 1))
    (hrank : rank ≤ (full.length + q + 1))
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 303))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 138 ∧
      RegistersFit (indexWidth 32 full.length q) (natRun (rawIncidenceROM q full) containing 138 state) := by
  let rom := rawIncidenceROM q full
  let B := 16
  let M := (full.length + q + 1)
  have hb : 16 ≤ B := (show 16 ≤ 16 from le_rfl)
  let tested := runOps rom (testWorkspace 2 (start + 172)) state
  have ht := testWorkspace_effect rom 2 (start + 172) state
  have th : tested.heap = state.heap := ht.1
  have rt : RankReady B M left right rank (5 * (start + 47)) tested := by
    refine ⟨(congrFun th _).trans ready.base_cell, (congrFun th _).trans ready.count_cell,
      (congrFun th _).trans ready.left_cell, (congrFun th _).trans ready.right_cell,
      (congrFun th _).trans ready.rank_cell, ?_, ht.2.2.trans ready.active⟩
    have hp := ht.2.1
    rw [ready.base_cell, ready.count_cell, ready.right_cell,
      ite_eq_right (Nat.sub_ne_zero_of_lt hr), ready.pc] at hp
    change tested.pc = _ at hp
    omega
  have tt : InputTables B M (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) tested := by
    rw [InputTables, th]
    exact htables
  have ss := chunk_of_macro q full containing start hbound hcode .innerTest state ready.pc ready.active
    (testWorkspace_safe q full 2 (start + 172) (by omega) state hf ready.base_cell
      (by rw [ready.count_cell]; exact count_fits _ _)
      (by rw [ready.right_cell]; exact scalar_fits _ _ _ (by omega))
      (lt_of_le_of_lt (by omega) hend))
  rw [chunk_run q full containing start hbound hcode .innerTest state ready.pc ready.active] at ss
  have cm := comparison_safe q full tested ss.2 rt.base_cell rt.count_cell
    (by rw [rt.left_cell]; exact hl) (by rw [rt.right_cell]; exact hr)
    (by rw [rt.rank_cell]; exact hrank) tt
  have cs := chunk_of_macro q full containing start hbound hcode .compare tested rt.pc rt.active cm
  rw [chunk_run q full containing start hbound hcode .compare tested rt.pc rt.active] at cs
  let compared := runOps rom comparison tested
  have cn := comparison_ready rom start B M left right rank (RawCandidateStableOrder.candidateCard q full)
    (RawCandidateOrder.keepCandidate q full) tested hb rt tt hl hr
  have rc := cn.1
  have tm := tail_safe q full 2 (start + 34) (by omega) compared cs.2 rc.base_cell
    (by rw [rc.right_cell]; exact scalar_fits _ _ _ (by omega)) (lt_of_le_of_lt (by omega) hend)
  have ts := chunk_of_macro q full containing start hbound hcode .innerTail compared rc.pc rc.active tm
  dsimp only [chunkLength] at ss cs ts
  have runTest : natRun rom containing 13 state = tested :=
    run_innerTest rom containing start hbound hcode state ready.pc ready.active
  have runCompare : natRun rom containing 110 tested = compared :=
    run_comparison rom containing start hbound hcode tested rt.pc rt.active
  have remainder : PrefixSafe (SafePoint q full containing start) rom containing tested (110 + 15) := by
    apply PrefixSafe.add _ _ _ _ _ _ cs.1
    rw [runCompare]
    exact ts.1
  constructor
  · change PrefixSafe _ _ _ _ (13 + (110 + 15))
    apply PrefixSafe.add _ _ _ _ _ _ ss.1
    rw [runTest]
    exact remainder
  · rw [show 138 = 13 + (110 + 15) by decide, natRun_add, runTest, natRun_add, runCompare]
    exact ts.2

theorem rank_scan_partial_safe (left : Nat) (state : NatState)
    (ready : RankReady 16 (full.length + q + 1) left 0 0 (5 * (start + 34)) state)
    (htables : InputTables 16 (full.length + q + 1)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hl : left < (full.length + q + 1))
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 303)))
    (upto : Nat) (hupto : upto ≤ (full.length + q + 1)) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (138 * upto) ∧
      RegistersFit (indexWidth 32 full.length q) (natRun (rawIncidenceROM q full) containing (138 * upto) state) := by
  revert hupto
  induction upto with
  | zero => intro _; exact ⟨by intro clock hc; omega, hf⟩
  | succ upto ih =>
    intro hupto
    obtain ⟨safe, fits⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing (138 * upto) state
    have pn := RawCandidateOrderingRAM.rank_scan_partial (rawIncidenceROM q full) containing start hbound hcode
      16 (full.length + q + 1) left (RawCandidateStableOrder.candidateCard q full)
      (RawCandidateOrder.keepCandidate q full) state ((show 16 ≤ 16 from le_rfl)) ready htables hl upto (by omega)
    have step := inner_iteration_safe q full containing start hbound hcode left upto _ previous pn.1 pn.2.1 hl
      (by omega) ((rankCount_le _ _ _ _).trans (by omega)) fits hend
    constructor
    · rw [Nat.mul_succ]
      exact PrefixSafe.add _ _ _ _ _ _ safe step.1
    · rw [Nat.mul_succ, natRun_add]
      exact step.2

theorem rank_scan_safe (left : Nat) (state : NatState)
    (ready : RankReady 16 (full.length + q + 1) left 0 0 (5 * (start + 34)) state)
    (htables : InputTables 16 (full.length + q + 1)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hl : left < (full.length + q + 1))
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 303))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (138 * (full.length + q + 1) + 13) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (138 * (full.length + q + 1) + 13) state) := by
  let M := (full.length + q + 1)
  have ss := rank_scan_partial_safe q full containing start hbound hcode left state ready htables hl hf hend M le_rfl
  have sn := RawCandidateOrderingRAM.rank_scan_partial (rawIncidenceROM q full) containing start hbound hcode
    16 M left (RawCandidateStableOrder.candidateCard q full)
    (RawCandidateOrder.keepCandidate q full) state ((show 16 ≤ 16 from le_rfl)) ready htables hl M le_rfl
  let previous := natRun (rawIncidenceROM q full) containing (138 * M) state
  have rp := sn.1
  have ts := chunk_of_macro q full containing start hbound hcode .innerTest previous rp.pc rp.active
    (testWorkspace_safe q full 2 (start + 172) (by omega) previous ss.2 rp.base_cell
      (by rw [rp.count_cell]; exact count_fits _ _)
      (by rw [rp.right_cell]; exact count_fits _ _) (lt_of_le_of_lt (by omega) hend))
  constructor
  · exact PrefixSafe.add _ _ _ _ _ _ ss.1 ts.1
  · rw [natRun_add]
    exact ts.2

theorem outer_iteration_safe (left : Nat) (state : NatState)
    (ready : OuterReady 16 (full.length + q + 1) left (5 * (start + 9)) state)
    (htables : InputTables 16 (full.length + q + 1)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hl : left < (full.length + q + 1)) (hcount : state.heap 0 ≤ (full.length + q + 1))
    (hord : OrdFits q full state) (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 303))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (138 * (full.length + q + 1) + 154) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (138 * (full.length + q + 1) + 154) state) := by
  let rom := rawIncidenceROM q full
  let B := 16
  let M := (full.length + q + 1)
  have hb : 16 ≤ B := (show 16 ≤ 16 from le_rfl)
  let tested := runOps rom (testWorkspace 1 (start + 288)) state
  have ht := testWorkspace_effect rom 1 (start + 288) state
  have th : tested.heap = state.heap := ht.1
  have tp : tested.pc = 5 * (start + 22) := by
    have hp := ht.2.1
    rw [ready.base_cell, ready.count_cell, ready.left_cell,
      ite_eq_right (Nat.sub_ne_zero_of_lt hl), ready.pc] at hp
    change tested.pc = _ at hp
    omega
  have ta : tested.halted = false := ht.2.2.trans ready.active
  have ts := chunk_of_macro q full containing start hbound hcode .outerTest state ready.pc ready.active
    (testWorkspace_safe q full 1 (start + 288) (by omega) state hf ready.base_cell
      (by rw [ready.count_cell]; exact count_fits _ _)
      (by rw [ready.left_cell]; exact scalar_fits _ _ _ (by omega)) (lt_of_le_of_lt (by omega) hend))
  rw [chunk_run q full containing start hbound hcode .outerTest state ready.pc ready.active] at ts
  let initialized := runOps rom rowInit tested
  have init := chunk_of_macro q full containing start hbound hcode .rowInit tested tp ta
    (rowInit_safe q full tested ts.2 ((congrFun th 8).trans ready.base_cell))
  rw [chunk_run q full containing start hbound hcode .rowInit tested tp ta] at init
  have ih : initialized.heap = Function.update (Function.update state.heap (B + 2) 0) (B + 3) 0 := by
    have hh := rowInit_heap rom tested (by rw [th, ready.base_cell])
    simpa only [th, ready.base_cell] using hh
  have ri : RankReady B M left 0 0 (5 * (start + 34)) initialized := by
    constructor
    · rw [ih]; simpa (disch := omega) using ready.base_cell
    · rw [ih]; simpa using ready.count_cell
    · rw [ih]; simpa using ready.left_cell
    · rw [ih]; simp
    · rw [ih]; simp
    · rw [show initialized = runOps rom rowInit tested from rfl,
        runOps_pc rom rowInit tested (by simp [rowInit, setWorkspace, storeWorkspace, loadCell, NoJump]), rowInit_length, tp]
      omega
    · exact (runOps_halted _ _ _).trans ta
  have fi : InnerFrame B state initialized := by
    intro address hj hr _h1 _h2 _h3 _h4 _h5
    rw [ih]
    simp [hj, hr]
  have ti := InputTables.of_innerFrame B M _ _ hb htables fi
  have rs := rank_scan_safe q full containing start hbound hcode left initialized ri ti hl init.2 hend
  have rn := RawCandidateOrderingRAM.rank_scan rom containing start hbound hcode B M left
    (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) initialized hb ri ti hl
  let ranked := natRun rom containing (138 * M + 13) initialized
  have rr := rn.1
  have tr := rn.2.1
  have fr : InnerFrame B state ranked := InnerFrame.trans B fi rn.2.2
  have ordf : OrdFits q full ranked := hord.of_innerFrame fr
  let rank := rankCount (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) left M
  have hrank : rank < M := rankCount_lt _ _ _ _ hl
  have rankedKeep : ranked.heap (arraySlot B M 1 (ranked.heap (B + 1))) ≤ 1 := by
    rw [rr.left_cell, tr.2 left hl]
    exact RawCandidateOrderingWord.bit_le_one _
  have rankedOrd : Fits (indexWidth 32 full.length q)
      (ranked.heap (arraySlot B M 2 (ranked.heap (B + 3)))) := by
    rw [rr.rank_cell]
    exact ordf rank hrank
  have rankedCount : ranked.heap 0 ≤ M := by
    rw [fr 0 (by omega) (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hcount
  have fm := finishRow_safe q full ranked rs.2 rr.base_cell rr.count_cell
    (by rw [rr.left_cell]; exact hl) (by rw [rr.rank_cell]; exact hrank) rankedKeep rankedOrd rankedCount
  have fs := chunk_of_macro q full containing start hbound hcode .finishRow ranked rr.pc rr.active fm
  rw [chunk_run q full containing start hbound hcode .finishRow ranked rr.pc rr.active] at fs
  let written := runOps rom finishRow ranked
  have wn := finishRow_ready rom start B M left M rank (RawCandidateStableOrder.candidateCard q full)
    (RawCandidateOrder.keepCandidate q full) ranked hb rr tr hl hrank
  have rw' := wn.1
  have tm := tail_safe q full 1 (start + 9) (by omega) written fs.2 rw'.base_cell
    (by rw [rw'.left_cell]; exact scalar_fits _ _ _ (by omega)) (lt_of_le_of_lt (by omega) hend)
  have tail := chunk_of_macro q full containing start hbound hcode .outerTail written rw'.pc rw'.active tm
  dsimp only [chunkLength] at ts init fs tail
  have runTest : natRun rom containing 13 state = tested := run_outerTest rom containing start hbound hcode state ready.pc ready.active
  have runInit : natRun rom containing 12 tested = initialized := run_rowInit rom containing start hbound hcode tested tp ta
  have runFinish : natRun rom containing 101 ranked = written := run_finishRow rom containing start hbound hcode ranked rr.pc rr.active
  have finishSafe : PrefixSafe (SafePoint q full containing start) rom containing ranked (101 + 15) := by
    apply PrefixSafe.add _ _ _ _ _ _ fs.1
    rw [runFinish]
    exact tail.1
  have rankSafe : PrefixSafe (SafePoint q full containing start) rom containing initialized ((138 * M + 13) + (101 + 15)) :=
    PrefixSafe.add _ _ _ _ _ _ rs.1 finishSafe
  have initSafe : PrefixSafe (SafePoint q full containing start) rom containing tested (12 + ((138 * M + 13) + (101 + 15))) := by
    apply PrefixSafe.add _ _ _ _ _ _ init.1
    rw [runInit]
    exact rankSafe
  have hclock : 138 * M + 154 = 13 + (12 + ((138 * M + 13) + (101 + 15))) := by omega
  constructor
  · rw [hclock]
    apply PrefixSafe.add _ _ _ _ _ _ ts.1
    rw [runTest]
    exact initSafe
  · rw [hclock, natRun_add, runTest, natRun_add, runInit, natRun_add]
    change RegistersFit _ (natRun rom containing (101 + 15) ranked)
    rw [natRun_add, runFinish]
    exact tail.2

omit hbound hcode in
theorem processedCount_le (keep : Nat → Bool) (upto : Nat) : processedCount keep upto ≤ upto := by
  simpa only [processedCount, List.length_range] using List.length_filter_le keep (List.range upto)

theorem outer_scan_partial_safe (state : NatState)
    (ready : OuterReady 16 (full.length + q + 1) 0 (5 * (start + 9)) state)
    (htables : InputTables 16 (full.length + q + 1)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hzero : state.heap 0 = 0) (hord : OrdFits q full state)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 303)))
    (upto : Nat) (hupto : upto ≤ (full.length + q + 1)) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        ((138 * (full.length + q + 1) + 154) * upto) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing ((138 * (full.length + q + 1) + 154) * upto) state) := by
  revert hupto
  induction upto with
  | zero => intro _; exact ⟨by intro clock hc; omega, hf⟩
  | succ upto ih =>
    intro hupto
    obtain ⟨safe, fits⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing ((138 * (full.length + q + 1) + 154) * upto) state
    have pn := RawCandidateOrderingRAM.outer_scan_partial (rawIncidenceROM q full) containing start hbound hcode q full
      16 state ((show 16 ≤ 16 from le_rfl)) ready htables hzero upto ((Nat.le_succ upto).trans hupto)
    have po := outer_scan_partial_ordFits q full containing start hbound hcode state ready htables hzero hord upto (by omega)
    have pcEq : previous.heap 0 = processedCount (RawCandidateOrder.keepCandidate q full) upto := pn.2.2.1.counter
    have pc : previous.heap 0 ≤ (full.length + q + 1) := by
      rw [pcEq]
      exact (processedCount_le _ _).trans (by omega)
    have step := outer_iteration_safe q full containing start hbound hcode upto previous pn.1 pn.2.1 (by omega) pc po fits hend
    constructor
    · rw [Nat.mul_succ]
      exact PrefixSafe.add _ _ _ _ _ _ safe step.1
    · rw [Nat.mul_succ, natRun_add]
      exact step.2

/-- The complete dynamic count-ranking program is prefix-safe from the
actual retention tables and ordinary initial ord-word bounds. -/
theorem sort_nat_safe (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (htables : InputTables 16 (full.length + q + 1)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hord : OrdFits q full state) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 303))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (totalSteps (full.length + q + 1)) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (totalSteps (full.length + q + 1)) state) := by
  let rom := rawIncidenceROM q full
  let B := 16
  let M := (full.length + q + 1)
  have hb : 16 ≤ B := (show 16 ≤ 16 from le_rfl)
  let initialized := runOps rom initCode state
  have init := chunk_of_macro q full containing start hbound hcode .initialize state
    (by simpa only [chunkOffset, Nat.add_zero] using hpc) ha (initialize_safe q full state hf hptr)
  rw [chunk_run q full containing start hbound hcode .initialize state
    (by simpa only [chunkOffset, Nat.add_zero] using hpc) ha] at init
  have ih : initialized.heap = Function.update (Function.update state.heap 0 0) (B + 1) 0 := by
    simpa only [hptr] using initCode_heap rom state
  have ri : OuterReady B M 0 (5 * (start + 9)) initialized := by
    constructor
    · rw [ih]; simpa (disch := omega) using hptr
    · rw [ih]; simpa (disch := omega) using hheader
    · rw [ih]; simp
    · rw [show initialized = runOps rom initCode state from rfl,
        runOps_pc rom initCode state (by simp [initCode, setCell, storeCell, setWorkspace, storeWorkspace, loadCell, NoJump]),
        initCode_length, hpc]
      omega
    · exact (runOps_halted _ _ _).trans ha
  have ti : InputTables B M (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) initialized := by
    constructor
    · intro index hi
      rw [ih]
      simpa (disch := omega) [arraySlot] using htables.1 index hi
    · intro index hi
      rw [ih]
      simpa (disch := omega) [arraySlot] using htables.2 index hi
  have oi : OrdFits q full initialized := by
    intro position hp
    rw [ih]
    simpa (disch := omega) [arraySlot] using hord position hp
  have iz : initialized.heap 0 = 0 := by rw [ih]; simp (disch := omega)
  have scan := outer_scan_partial_safe q full containing start hbound hcode initialized ri ti iz oi init.2 hend M le_rfl
  have sn := RawCandidateOrderingRAM.outer_scan_partial rom containing start hbound hcode q full B initialized hb ri ti iz M le_rfl
  let scanned := natRun rom containing ((138 * M + 154) * M) initialized
  have rs : OuterReady B M M (5 * (start + 9)) scanned := sn.1
  have ts := chunk_of_macro q full containing start hbound hcode .outerTest scanned rs.pc rs.active
    (testWorkspace_safe q full 1 (start + 288) (by omega) scanned scan.2 rs.base_cell
      (by rw [rs.count_cell]; exact count_fits _ _)
      (by rw [rs.left_cell]; exact count_fits _ _) (lt_of_le_of_lt (by omega) hend))
  rw [chunk_run q full containing start hbound hcode .outerTest scanned rs.pc rs.active] at ts
  let tested := runOps rom (testWorkspace 1 (start + 288)) scanned
  have ht := testWorkspace_effect rom 1 (start + 288) scanned
  have th : tested.heap = scanned.heap := ht.1
  have tp : tested.pc = 5 * (start + 288) := by
    simpa only [rs.base_cell, rs.count_cell, rs.left_cell, Nat.sub_self, ite_true] using ht.2.1
  have ta : tested.halted = false := ht.2.2.trans rs.active
  have countEq : scanned.heap 0 = processedCount (RawCandidateOrder.keepCandidate q full) M := sn.2.2.1.counter
  have tc : tested.heap 0 ≤ M := by
    rw [th, countEq]
    exact processedCount_le _ _
  have fm := finishCode_safe q full tested ts.2 ((congrFun th 8).trans rs.base_cell)
    ((congrFun th B).trans rs.count_cell) tc
  have fs := chunk_of_macro q full containing start hbound hcode .finish tested tp ta fm
  dsimp only [chunkLength] at init ts fs
  have runInit : natRun rom containing 9 state = initialized := run_initCode rom containing start hbound hcode state hpc ha
  have runTest : natRun rom containing 13 scanned = tested := run_outerTest rom containing start hbound hcode scanned rs.pc rs.active
  have rest : PrefixSafe (SafePoint q full containing start) rom containing scanned (13 + 15) := by
    apply PrefixSafe.add _ _ _ _ _ _ ts.1
    rw [runTest]
    exact fs.1
  have afterInit : PrefixSafe (SafePoint q full containing start) rom containing initialized
      (((138 * M + 154) * M) + (13 + 15)) := PrefixSafe.add _ _ _ _ _ _ scan.1 rest
  have hclock : totalSteps M = 9 + (((138 * M + 154) * M) + (13 + 15)) := by
    rw [totalSteps, Nat.mul_comm M (138 * M + 154)]
    omega
  constructor
  · rw [hclock]
    apply PrefixSafe.add _ _ _ _ _ _ init.1
    rw [runInit]
    exact afterInit
  · rw [hclock, natRun_add, runInit, natRun_add]
    change RegistersFit _ (natRun rom containing (13 + 15) scanned)
    rw [natRun_add, runTest]
    exact fs.2

theorem natRun_prefix_safe (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (htables : InputTables 16 (full.length + q + 1)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hord : OrdFits q full state) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 303)))
    (count : Nat) (hc : count ≤ totalSteps (full.length + q + 1)) :
    let result := natRun (rawIncidenceROM q full) containing count state
    RegistersFit (indexWidth 32 full.length q) result ∧ Fits (indexWidth 32 full.length q) result.pc ∧ result.halted = false := by
  have hs := sort_nat_safe q full containing start hbound hcode state hf hptr hheader htables hord hpc ha hend
  by_cases heq : count = totalSteps (full.length + q + 1)
  · subst count
    have hn : Sorted q full 16 start state
        (natRun (rawIncidenceROM q full) containing (totalSteps (full.length + q + 1)) state) :=
      RawCandidateOrderingRAM.sort (rawIncidenceROM q full) containing start hbound hcode q full
        16 state ((show 16 ≤ 16 from le_rfl)) hptr hheader htables hpc ha
    exact ⟨hs.2, by rw [hn.returned.pc]; exact hend, hn.returned.active⟩
  · have hp := hs.1 count (by omega)
    obtain ⟨offset, hoff, pc, active, _⟩ := hp.2
    exact ⟨hp.1, by rw [pc]; exact lt_of_le_of_lt (by omega) hend, active⟩


omit hbound hcode in
private theorem input_prefix (initialUsed : Finset (Fin q)) :
    PA06A19PrepareROM001.ROMPrefix (rawIncidenceROM q full)
      (CompactControllerClaims.controllerInput q full initialUsed) :=
  PA06A19PrepareROM001.inputTail_prefix _
    ((List.finRange q).map (fun tool => bit (decide (tool ∈ initialUsed))))

theorem word_run_eq_nat (initialUsed : Finset (Fin q)) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16) (hheader : state.heap 16 = full.length + q + 1)
    (htables : InputTables 16 (full.length + q + 1) (RawCandidateStableOrder.candidateCard q full)
      (RawCandidateOrder.keepCandidate q full) state)
    (hord : OrdFits q full state) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 303)))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ totalSteps (full.length + q + 1)) :
    packingRun (CompactControllerClaims.controllerInput q full initialUsed) containing count
      (state.toWord (indexWidth 32 full.length q)) =
        (natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 32 full.length q) := by
  have safe := sort_nat_safe q full containing start hbound hcode state hf hptr hheader htables hord hpc ha hend
  have rawEq (k : Nat) (hk : k ≤ totalSteps (full.length + q + 1)) :
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

theorem word_prefix_safe (initialUsed : Finset (Fin q)) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16) (hheader : state.heap 16 = full.length + q + 1)
    (htables : InputTables 16 (full.length + q + 1) (RawCandidateStableOrder.candidateCard q full)
      (RawCandidateOrder.keepCandidate q full) state)
    (hord : OrdFits q full state) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 303)))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode containing))
    (count : Nat) (hc : count < totalSteps (full.length + q + 1)) :
    let runtime := CompactControllerClaims.controllerInput q full initialUsed
    let actual := packingRun runtime containing count (state.toWord (indexWidth 32 full.length q))
    actual.halted = false ∧ actual.pc.toNat + 4 < (packingCode containing).length ∧
      ∃ op, PackingOp.decode (fetch containing actual) = some op ∧ packingAccessFits runtime (linearLimit full.length q) actual op := by
  have point := (sort_nat_safe q full containing start hbound hcode state hf hptr hheader htables hord hpc ha hend).1 count hc
  have pcFit := point.pcFits hend
  obtain ⟨registers, offset, hoff, pc, active, op, decoded, access⟩ := point
  dsimp only
  rw [word_run_eq_nat q full containing start hbound hcode initialUsed state hf hptr hheader htables hord hpc ha hend hwords count hc.le]
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
        (by simpa only [NatAccessFits] using access)
    | arithmetic operation target left right => trivial
    | jumpIfZero condition target => trivial

theorem sort_word (initialUsed : Finset (Fin q)) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16) (hheader : state.heap 16 = full.length + q + 1)
    (htables : InputTables 16 (full.length + q + 1) (RawCandidateStableOrder.candidateCard q full)
      (RawCandidateOrder.keepCandidate q full) state)
    (hord : OrdFits q full state) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 303)))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode containing)) :
    let result := natRun (rawIncidenceROM q full) containing (totalSteps (full.length + q + 1)) state
    packingRun (CompactControllerClaims.controllerInput q full initialUsed) containing (totalSteps (full.length + q + 1))
      (state.toWord (indexWidth 32 full.length q)) = result.toWord (indexWidth 32 full.length q) ∧
      Sorted q full 16 start state result :=
  ⟨word_run_eq_nat q full containing start hbound hcode initialUsed state hf hptr hheader htables hord hpc ha hend hwords _ le_rfl,
    RawCandidateOrderingRAM.sort (rawIncidenceROM q full) containing start hbound hcode q full 16 state (by decide)
      hptr hheader htables hpc ha⟩

end Linked

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactOrdering034Loop


