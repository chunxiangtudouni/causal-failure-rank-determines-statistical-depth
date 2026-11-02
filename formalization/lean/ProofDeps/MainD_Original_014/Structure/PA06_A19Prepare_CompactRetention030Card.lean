module

public import Structure.PA06_A19Prepare_CompactRetention030Parts

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Actual B16 card phase. Original generic Nat query/frame facts and clocks
are reused. Each executed small-piece source requirement is discharged;
the125-op query is020's actual full-width loop, not a safety premise. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention030Card

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateRetentionRAM
open PA06A19PrepareCompactRetention030Parts (SafePoint piece_safe piece_run)

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 398 ≤ containing.length)
  (hcode : ∀ position < 398, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem card_phase_safe (index : Nat) (hi : index < full.length + q + 1) (state : NatState)
    (hptr : state.heap 8 = 16)
    (hcount : state.heap 16 = full.length + q + 1)
    (hindex : state.heap (16 + 1) = index)
    (hpc : state.pc = 5 * (start + 6)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
      (cardPhaseSteps full.length q index) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (cardPhaseSteps full.length q index) state) := by
  let rom := rawIncidenceROM q full
  let B := 16
  let tested := runOps rom (testWorkspace 1 (start + 398)) state
  have ht := testWorkspace_values rom 1 (start + 398) state
  have th : tested.heap = state.heap := ht.1
  have tp : tested.pc = 5 * (start + 19) := by
    have hp := ht.2.1
    rw [hptr, hcount, hindex] at hp
    simp only [Nat.sub_ne_zero_of_lt hi, ite_false, hpc] at hp
    change tested.pc = _ at hp
    omega
  have ta : tested.halted = false := ht.2.2.trans ha
  have tb : tested.heap 8 = B := by rw [th]; exact hptr
  have ti : tested.heap (B + 1) = index := by rw [th]; exact hindex
  have ts := piece_safe q full containing start hbound hcode .outerTest state hpc ha hf
    ⟨hptr, hcount, by rw [hindex]; exact hi.le⟩ hend
  have tr : natRun rom containing 13 state = tested := piece_run q full containing start hbound hcode .outerTest state hpc ha
  dsimp only [RawCandidateRetentionWordChunks.chunkLength] at ts
  rw [tr] at ts
  let arguments := runOps rom cardArguments tested
  have av := cardArguments_values rom B tested tb
  have ah : arguments.heap = Function.update (Function.update state.heap 1 index) 2 0 := by
    simpa only [th, B, hindex] using av.1
  have above (address : Nat) (haddr : 8 ≤ address) : arguments.heap address = state.heap address := by
    rw [ah]
    simp [show address ≠ 1 by omega, show address ≠ 2 by omega]
  have ap : arguments.pc = 5 * (start + 29) := by
    have hp := av.2.1
    rw [tp] at hp
    change arguments.pc = _ at hp
    omega
  have aa : arguments.halted = false := av.2.2.trans ta
  have ars := piece_safe q full containing start hbound hcode .cardArgs tested tp ta ts.2
    ⟨tb, by rw [ti]; exact hi.le⟩ hend
  have ar : natRun rom containing 10 tested = arguments := piece_run q full containing start hbound hcode .cardArgs tested tp ta
  dsimp only [RawCandidateRetentionWordChunks.chunkLength] at ars
  rw [ar] at ars
  let steps := RawCandidatePairScan.totalSteps full.length index 0 q
  let scanned := natRun rom containing steps arguments
  have hl : arguments.heap 1 = index := by rw [ah]; simp
  have hr : arguments.heap 2 = 0 := by rw [ah]; simp
  have zero : 0 < full.length + q + 1 := by omega
  have ps := PA06A19PrepareCompactRetention030Parts.pair_safe q full containing start hbound hcode 29 (Or.inl rfl)
    ⟨index, hi⟩ ⟨0, zero⟩ arguments ap aa hl hr ars.2 hend
  have slice := RawCandidateRetentionWordSafety.pair_slice containing start hbound hcode 29 (Or.inl rfl)
  have sem := RawCandidatePairScan.scan q full containing (start + 29) slice.1 slice.2
    ⟨index, hi⟩ ⟨0, zero⟩ arguments ap aa hl hr
  dsimp only at sem
  rcases sem with ⟨_q, _cursor, c4, _c5, _c6, frame, sp, sa⟩
  have sb : scanned.heap 8 = B :=
    (frame 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((above 8 le_rfl).trans hptr)
  have s1 : scanned.heap 1 = index :=
    (frame 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl
  have s4 : scanned.heap 4 ≤ q := by
    rw [show scanned.heap 4 = _ from c4]
    simpa only [Fintype.card_fin] using Finset.card_le_univ
      (((RawCandidateOrder.candidateSupports q full).getD index ∅) ∩
        ((RawCandidateOrder.candidateSupports q full).getD 0 ∅))
  have spc : scanned.pc = 5 * (start + 154) := by
    change scanned.pc = 5 * (start + 29 + 125) at sp
    omega
  have ats := piece_safe q full containing start hbound hcode .afterCard scanned spc sa ps.2
    ⟨sb, by rw [s1]; exact hi.le, s4⟩ hend
  dsimp only [RawCandidateRetentionWordChunks.chunkLength] at ats
  have safeArgs : PrefixSafe (SafePoint q full containing start) rom containing state (13 + 10) := by
    apply PrefixSafe.add _ _ _ _ 13 10 ts.1
    rw [tr]
    exact ars.1
  have safePair : PrefixSafe (SafePoint q full containing start) rom containing state ((13 + 10) + steps) := by
    apply PrefixSafe.add _ _ _ _ (13 + 10) steps safeArgs
    rw [natRun_add, tr, ar]
    exact ps.1
  have allSafe : PrefixSafe (SafePoint q full containing start) rom containing state (((13 + 10) + steps) + 26) := by
    apply PrefixSafe.add _ _ _ _ ((13 + 10) + steps) 26 safePair
    rw [natRun_add, natRun_add, tr, ar]
    exact ats.1
  have hclock : cardPhaseSteps full.length q index = ((13 + 10) + steps) + 26 := by
    unfold cardPhaseSteps
    dsimp only [steps]
    omega
  refine ⟨by simpa only [hclock] using allSafe, ?_⟩
  rw [hclock, natRun_add, natRun_add, natRun_add, tr, ar]
  exact ats.2


end Linked

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention030Card

