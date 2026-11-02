module

public import Structure.PA06_A19Prepare_CompactRetention030Card

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Actual later-candidate loop safety at B16/full width32. The original
Nat inner_iteration/scan semantics establish counters, flags and frames;
new safety composition uses only030's real small pieces and020 PairScan.
No original distant workspace, oldFit16 or completed hSafe is granted. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention030Inner

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM
  RawCandidateRetentionRAM
open PA06A19PrepareCompactRetention030Parts (SafePoint piece_run)
open RawCandidateRetentionWordChunks (Chunk chunkCode chunkOffset chunkLength)

structure Ready (q : Nat) (full : List (Finset (Fin q))) (index later pointer : Nat) (state : NatState) : Prop where
  ptr : state.heap 8 = 16
  header : state.heap 16 = (full.length + q + 1)
  index_cell : state.heap (16 + 1) = index
  later_cell : state.heap (16 + 2) = later
  flag_le : state.heap (16 + 3) ≤ 1
  pc : state.pc = pointer
  active : state.halted = false

def Frame (q : Nat) (_full : List (Finset (Fin q))) (before after : NatState) : Prop :=
  ∀ address, 8 ≤ address → address ≠ 16 + 2 →
    address ≠ 16 + 3 → after.heap address = before.heap address

theorem Frame.refl (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Frame q full state state :=
  fun _ _ _ _ => rfl

theorem Frame.trans {q : Nat} {full : List (Finset (Fin q))} {one two three : NatState}
    (h12 : Frame q full one two) (h23 : Frame q full two three) : Frame q full one three := by
  intro address ha h2 h3
  exact (h23 address ha h2 h3).trans (h12 address ha h2 h3)

theorem frame_of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {before after : NatState}
    (hh : after.heap = before.heap) : Frame q full before after := fun address _ _ _ => congrFun hh address

theorem Ready.of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {index later pointer nextPointer : Nat}
    {before after : NatState} (ready : Ready q full index later pointer before)
    (hh : after.heap = before.heap) (hp : after.pc = nextPointer) (ha : after.halted = false) :
    Ready q full index later nextPointer after :=
  ⟨(congrFun hh _).trans ready.ptr, (congrFun hh _).trans ready.header,
    (congrFun hh _).trans ready.index_cell, (congrFun hh _).trans ready.later_cell,
    (congrFun hh _).le.trans ready.flag_le, hp, ha⟩

theorem Ready.of_frame {q : Nat} {full : List (Finset (Fin q))} {index later nextLater pointer nextPointer : Nat}
    {before after : NatState} (ready : Ready q full index later pointer before)
    (frame : Frame q full before after)
    (hj : after.heap (16 + 2) = nextLater)
    (hf : after.heap (16 + 3) ≤ 1)
    (hp : after.pc = nextPointer) (ha : after.halted = false) : Ready q full index nextLater nextPointer after := by
  refine ⟨(frame 8 le_rfl (by omega) (by omega)).trans ready.ptr,
    (frame _ (by omega) (by omega) (by omega)).trans ready.header,
    (frame _ (by omega) (by omega) (by omega)).trans ready.index_cell, hj, hf, hp, ha⟩

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 398 ≤ containing.length)
  (hcode : ∀ position < 398, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem inner_iteration_safe (index later : Nat) (state : NatState)
    (hi : index < (full.length + q + 1)) (hj : later < (full.length + q + 1))
    (ready : Ready q full index later (5 * (start + 180)) state)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398))) :
    let result := natRun (rawIncidenceROM q full) containing (innerIterationSteps full.length q index later) state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (innerIterationSteps full.length q index later) ∧
      RegistersFit (indexWidth 32 full.length q) result ∧ Ready q full index (later + 1) (5 * (start + 180)) result ∧
      result.heap 1 = index ∧ Frame q full state result := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (testWorkspace 2 (start + 364)) state
  have ht := testWorkspace_values rom 2 (start + 364) state
  dsimp only at ht
  have th : tested.heap = state.heap := ht.1
  have tp : tested.pc = 5 * (start + 193) := by
    have hp := ht.2.1
    rw [ready.ptr, ready.header, ready.later_cell,
      ite_eq_right (Nat.sub_ne_zero_of_lt hj), ready.pc] at hp
    dsimp only [tested]
    omega
  have ta : tested.halted = false := ht.2.2.trans ready.active
  have ts := PA06A19PrepareCompactRetention030Parts.piece_safe q full containing start hbound hcode .innerTest state
    ready.pc ready.active hr ⟨ready.ptr, ready.header, ready.later_cell.le.trans hj.le⟩ hend
  rw [piece_run q full containing start hbound hcode .innerTest state ready.pc ready.active] at ts
  let arguments := runOps rom pairArguments tested
  have ar := pairArguments_values rom 16 tested ((congrFun th 8).trans ready.ptr)
  dsimp only at ar
  have hb := (show 16 ≤ 16 from le_rfl)
  have ah : arguments.heap = Function.update (Function.update state.heap 1 index) 2 later := by
    have hh := ar.1
    rw [th, ready.index_cell, Function.update_of_ne (by omega : 16 + 2 ≠ 1), ready.later_cell] at hh
    exact hh
  have aa (address : Nat) (ha : 8 ≤ address) : arguments.heap address = state.heap address := by
    rw [ah]
    simp (disch := omega)
  have ap : arguments.pc = 5 * (start + 207) := by
    have hp := ar.2.1
    rw [tp] at hp
    dsimp only [arguments]
    omega
  have aactive : arguments.halted = false := ar.2.2.trans ta
  have args := PA06A19PrepareCompactRetention030Parts.piece_safe q full containing start hbound hcode .pairArgs tested tp ta ts.2
    ⟨(congrFun th 8).trans ready.ptr, by rw [th, ready.index_cell]; exact hi.le,
      by rw [th, ready.later_cell]; exact hj.le⟩ hend
  rw [piece_run q full containing start hbound hcode .pairArgs tested tp ta] at args
  let pairSteps := RawCandidatePairScan.totalSteps full.length index later q
  let scanned := natRun rom containing pairSteps arguments
  have ps := PA06A19PrepareCompactRetention030Parts.pair_safe q full containing start hbound hcode 207 (Or.inr rfl)
    ⟨index, hi⟩ ⟨later, hj⟩ arguments ap aactive (by rw [ah]; simp) (by rw [ah]; simp) args.2 hend
  have slice := RawCandidateRetentionWordSafety.pair_slice containing start hbound hcode 207 (Or.inr rfl)
  have pair := RawCandidatePairScan.scan q full containing (start + 207) slice.1 slice.2
    ⟨index, hi⟩ ⟨later, hj⟩ arguments ap aactive (by rw [ah]; simp) (by rw [ah]; simp)
  dsimp only at pair
  rcases pair with ⟨_hq, _hcursor, _hinter, hleft, hright, pframe, pp, pa⟩
  have sa (address : Nat) (ha : 8 ≤ address) : scanned.heap address = state.heap address :=
    (pframe address (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (aa address ha)
  have sp : scanned.pc = 5 * (start + 332) := by dsimp only [scanned]; omega
  have hcard (set : Finset (Fin q)) : set.card ≤ q := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ set
  have sf5 : scanned.heap 5 ≤ q := hleft.le.trans (hcard _)
  have sf6 : scanned.heap 6 ≤ q := hright.le.trans (hcard _)
  have tail := PA06A19PrepareCompactRetention030Parts.piece_safe q full containing start hbound hcode .innerTail scanned sp pa ps.2
    ⟨(sa 8 le_rfl).trans ready.ptr, sf5, sf6,
      (sa _ (by omega)).le.trans ready.flag_le,
      by rw [sa _ (by omega), ready.later_cell]; exact hj.le⟩ hend
  have runTest : natRun rom containing 13 state = tested :=
    piece_run q full containing start hbound hcode .innerTest state ready.pc ready.active
  have runArgs : natRun rom containing 14 tested = arguments :=
    piece_run q full containing start hbound hcode .pairArgs tested tp ta
  have rest : PrefixSafe (SafePoint q full containing start) rom containing arguments (pairSteps + 32) :=
    PrefixSafe.add _ _ _ _ pairSteps 32 ps.1 tail.1
  have afterTest : PrefixSafe (SafePoint q full containing start) rom containing tested (14 + (pairSteps + 32)) := by
    apply PrefixSafe.add _ _ _ _ 14 _ args.1
    rw [runArgs]
    exact rest
  have allSafe : PrefixSafe (SafePoint q full containing start) rom containing state (13 + (14 + (pairSteps + 32))) := by
    apply PrefixSafe.add _ _ _ _ 13 _ ts.1
    rw [runTest]
    exact afterTest
  have hclock : innerIterationSteps full.length q index later = 13 + (14 + (pairSteps + 32)) := by
    dsimp only [innerIterationSteps, pairSteps]
    omega
  have resultFit : RegistersFit (indexWidth 32 full.length q)
      (natRun rom containing (innerIterationSteps full.length q index later) state) := by
    rw [hclock, natRun_add, runTest, natRun_add, runArgs, natRun_add]
    exact tail.2
  have hn := inner_iteration q full containing start hbound hcode 16 index later hb hi hj
    state ready.ptr ready.header ready.index_cell ready.later_cell ready.pc ready.active
  dsimp only at hn
  rcases hn with ⟨hj', hflag, _hraw, frame, pointer, active⟩
  have flag_le : (natRun rom containing (innerIterationSteps full.length q index later) state).heap
      (16 + 3) ≤ 1 := by
    rw [hflag]
    split
    · omega
    · exact ready.flag_le
  exact ⟨by simpa only [hclock] using allSafe, resultFit,
    ready.of_frame frame hj' flag_le pointer active, _hraw, frame⟩

end Linked

section Loop

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 398 ≤ containing.length)
  (hcode : ∀ position < 398, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem inner_scan_partial_safe (index first : Nat) (state : NatState)
    (hi : index < (full.length + q + 1))
    (ready : Ready q full index first (5 * (start + 180)) state)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398)))
    (count : Nat) (hc : first + count ≤ (full.length + q + 1)) :
    let clock := innerScanSteps full.length q index first count
    let result := natRun (rawIncidenceROM q full) containing clock state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state clock ∧
      RegistersFit (indexWidth 32 full.length q) result ∧
      Ready q full index (first + count) (5 * (start + 180)) result ∧
      (state.heap 1 = index → result.heap 1 = index) ∧ Frame q full state result := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [innerScanSteps, Finset.range_zero, Finset.sum_empty, natRun, Nat.add_zero] using
      (show PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 0 ∧
        RegistersFit (indexWidth 32 full.length q) state ∧ Ready q full index first (5 * (start + 180)) state ∧
        (state.heap 1 = index → state.heap 1 = index) ∧ Frame q full state state from
          ⟨by intro clock hclock; omega, hr, ready, fun h => h, Frame.refl _ _ state⟩)
  | succ count ih =>
    intro hc
    rcases ih (by omega) with ⟨safe, fits, previousReady, _previousRaw, frame⟩
    let previous := natRun (rawIncidenceROM q full) containing (innerScanSteps full.length q index first count) state
    have step := inner_iteration_safe q full containing start hbound hcode index (first + count) previous hi (by omega)
      previousReady fits hend
    dsimp only at step
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [innerScanSteps_succ]
      exact PrefixSafe.add _ _ _ _ _ _ safe step.1
    · rw [innerScanSteps_succ, natRun_add]
      exact step.2.1
    · rw [innerScanSteps_succ, natRun_add]
      simpa only [Nat.add_assoc] using step.2.2.1
    · intro _
      rw [innerScanSteps_succ, natRun_add]
      exact step.2.2.2.1
    · rw [innerScanSteps_succ, natRun_add]
      exact frame.trans step.2.2.2.2

theorem inner_scan_from_safe (index first : Nat) (state : NatState)
    (hi : index < (full.length + q + 1)) (hfirst : first ≤ (full.length + q + 1))
    (ready : Ready q full index first (5 * (start + 180)) state)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398))) :
    let clock := innerScanSteps full.length q index first ((full.length + q + 1) - first) + 13
    let result := natRun (rawIncidenceROM q full) containing clock state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state clock ∧
      RegistersFit (indexWidth 32 full.length q) result ∧
      Ready q full index (full.length + q + 1) (5 * (start + 364)) result ∧
      (state.heap 1 = index → result.heap 1 = index) ∧ Frame q full state result := by
  let count := (full.length + q + 1) - first
  have hsum : first + count = (full.length + q + 1) := by dsimp only [count]; omega
  rcases inner_scan_partial_safe q full containing start hbound hcode index first state hi ready hr hend count (by omega) with
    ⟨safe, fits, previousReady, raw, frame⟩
  let previous := natRun (rawIncidenceROM q full) containing (innerScanSteps full.length q index first count) state
  have rp : Ready q full index (full.length + q + 1) (5 * (start + 180)) previous := by
    simpa only [hsum] using previousReady
  let tested := runOps (rawIncidenceROM q full) (testWorkspace 2 (start + 364)) previous
  have ht := testWorkspace_values (rawIncidenceROM q full) 2 (start + 364) previous
  dsimp only at ht
  have th : tested.heap = previous.heap := ht.1
  have tp : tested.pc = 5 * (start + 364) := by
    have hp := ht.2.1
    rw [rp.ptr, rp.header, rp.later_cell, Nat.sub_self] at hp
    exact hp
  have ta : tested.halted = false := ht.2.2.trans rp.active
  have ts := PA06A19PrepareCompactRetention030Parts.piece_safe q full containing start hbound hcode .innerTest previous rp.pc rp.active fits
    ⟨rp.ptr, rp.header, rp.later_cell.le⟩ hend
  have runTest : natRun (rawIncidenceROM q full) containing 13 previous = tested :=
    piece_run q full containing start hbound hcode .innerTest previous rp.pc rp.active
  have allSafe : PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
      (innerScanSteps full.length q index first count + 13) := PrefixSafe.add _ _ _ _ _ _ safe ts.1
  have hrun : natRun (rawIncidenceROM q full) containing
      (innerScanSteps full.length q index first count + 13) state = tested := by
    rw [natRun_add, runTest]
  dsimp only
  change PrefixSafe _ _ _ _ (innerScanSteps full.length q index first count + 13) ∧ _
  refine ⟨allSafe, ?_⟩
  rw [hrun]
  refine ⟨?_, rp.of_heap_eq th tp ta, ?_, frame.trans (frame_of_heap_eq th)⟩
  · have hfit := ts.2
    change RegistersFit (indexWidth 32 full.length q) (natRun (rawIncidenceROM q full) containing 13 previous) at hfit
    rw [runTest] at hfit
    exact hfit
  · intro hraw
    exact (congrFun th 1).trans (raw hraw)

theorem inner_scan_safe (index : Nat) (state : NatState)
    (hi : index < (full.length + q + 1))
    (ready : Ready q full index (index + 1) (5 * (start + 180)) state)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398))) :
    let result := natRun (rawIncidenceROM q full) containing (innerCompleteSteps full.length q index) state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (innerCompleteSteps full.length q index) ∧
      RegistersFit (indexWidth 32 full.length q) result ∧
      Ready q full index (full.length + q + 1) (5 * (start + 364)) result ∧
      (state.heap 1 = index → result.heap 1 = index) ∧ Frame q full state result :=
  inner_scan_from_safe q full containing start hbound hcode index (index + 1) state hi (by omega) ready hr hend

end Loop


end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention030Inner

