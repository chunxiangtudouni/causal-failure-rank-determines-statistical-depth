module

public import Structure.PA06_A19Prepare_CompactRetention030Inner

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Full actual398-op retention safety, at the original B16 compact heap
and full word32. Existing Nat card/inner/outer semantics discharge data
facts.030/027/020 supply the real executed piece certificates. No hSafe,
oldFit16, retained answer or alternate program is a caller qualification. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention030Loop

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateRetentionRAM
open PA06A19PrepareCompactRetention030Parts (SafePoint piece_safe piece_run point_pcFits)

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 398 ≤ containing.length)
  (hcode : ∀ position < 398, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem outer_iteration_safe (index : Nat) (hi : index < (full.length + q + 1))
    (state : NatState) (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hindex : state.heap (16 + 1) = index)
    (hpc : state.pc = 5 * (start + 6)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
      (outerIterationSteps full.length q index) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (outerIterationSteps full.length q index) state) := by
  let rom := rawIncidenceROM q full
  let B := 16
  have hb : 16 ≤ B := (show 16 ≤ 16 from le_rfl)
  let seeded := natRun rom containing (cardPhaseSteps full.length q index) state
  have cs := PA06A19PrepareCompactRetention030Card.card_phase_safe q full containing start hbound hcode
    index hi state hptr hheader hindex hpc ha hf hend
  have cn := card_phase q full containing start hbound hcode B index hb hi state hptr hheader hindex hpc ha
  dsimp only at cn
  rcases cn with ⟨cj, cf, cr, _card, frame, cp, ca⟩
  have cb : seeded.heap 8 = B :=
    (frame 8 le_rfl (by omega) (by omega) (by unfold cardAddress; omega)).trans hptr
  have cm : seeded.heap B = (full.length + q + 1) :=
    (frame B (by omega) (by omega) (by omega) (by unfold cardAddress; omega)).trans hheader
  have ci : seeded.heap (B + 1) = index :=
    (frame (B + 1) (by omega) (by omega) (by omega) (by unfold cardAddress; omega)).trans hindex
  have cfle : seeded.heap (B + 3) ≤ 1 := by
    rw [cf]
    simp only [RawCandidateRetentionFlags.partialFlag, bit]
    split <;> omega
  have ready : PA06A19PrepareCompactRetention030Inner.Ready q full index (index + 1) (5 * (start + 180)) seeded :=
    ⟨cb, cm, ci, cj, cfle, cp, ca⟩
  have ins := PA06A19PrepareCompactRetention030Inner.inner_scan_safe q full containing start hbound hcode
    index seeded hi ready cs.2 hend
  dsimp only at ins
  let scanned := natRun rom containing (innerCompleteSteps full.length q index) seeded
  have sr := ins.2.2.1
  have raw : scanned.heap 1 = index := ins.2.2.2.1 cr
  have fs := piece_safe q full containing start hbound hcode .finish scanned sr.pc sr.active ins.2.1
    ⟨sr.ptr, sr.header, by rw [raw]; exact hi.le, by rw [sr.index_cell]; exact hi.le, sr.flag_le⟩ hend
  have first : PrefixSafe (SafePoint q full containing start) rom containing state
      (cardPhaseSteps full.length q index + innerCompleteSteps full.length q index) :=
    PrefixSafe.add _ _ _ _ _ _ cs.1 ins.1
  have allSafe : PrefixSafe (SafePoint q full containing start) rom containing state
      (cardPhaseSteps full.length q index + innerCompleteSteps full.length q index + 34) := by
    apply PrefixSafe.add _ _ _ _ _ _ first
    rw [natRun_add]
    exact fs.1
  refine ⟨allSafe, ?_⟩
  rw [outerIterationSteps, natRun_add, natRun_add]
  exact fs.2

theorem outer_scan_partial_safe (state : NatState)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hindex : state.heap (16 + 1) = 0)
    (hpc : state.pc = 5 * (start + 6)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398)))
    (count : Nat) (hc : count ≤ (full.length + q + 1)) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
      (outerScanSteps full.length q count) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (outerScanSteps full.length q count) state) := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [outerScanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 0 ∧
        RegistersFit (indexWidth 32 full.length q) state from ⟨by intro clock hclock; omega, hf⟩)
  | succ count ih =>
    intro hc
    obtain ⟨safe, fits⟩ := ih (by omega)
    let B := 16
    have hb : 16 ≤ B := (show 16 ≤ 16 from le_rfl)
    let previous := natRun (rawIncidenceROM q full) containing (outerScanSteps full.length q count) state
    have pn := outer_scan_partial q full containing start hbound hcode B hb state hptr hheader hindex hpc ha
      count ((Nat.le_succ count).trans hc)
    dsimp only at pn
    obtain ⟨pi, _arrays, frame, pp, pa⟩ := pn
    have pb : previous.heap 8 = B :=
      (frame 8 ⟨le_rfl, by omega, by omega, by omega, Or.inl (by omega)⟩).trans hptr
    have pm : previous.heap B = (full.length + q + 1) :=
      (frame B ⟨by omega, by omega, by omega, by omega, Or.inl (by omega)⟩).trans hheader
    have step := outer_iteration_safe q full containing start hbound hcode count (by omega)
      previous pb pm pi pp pa fits hend
    constructor
    · rw [outerScanSteps_succ]
      exact PrefixSafe.add _ _ _ _ _ _ safe step.1
    · rw [outerScanSteps_succ, natRun_add]
      exact step.2

/-- All real prefixes of the 398-op retention program are safe, including
the final test that returns active at the block's end.  No scratch values
or previously computed card/keep answers are inputs. -/
theorem retention_nat_safe (state : NatState)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398))) :
    let result := natRun (rawIncidenceROM q full) containing (totalSteps full.length q) state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
      (totalSteps full.length q) ∧ RegistersFit (indexWidth 32 full.length q) result ∧
      result.heap 8 = 16 ∧
      result.heap 16 = (full.length + q + 1) ∧
      result.pc = 5 * (start + 398) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let B := 16
  let M := (full.length + q + 1)
  have hb : 16 ≤ B := (show 16 ≤ 16 from le_rfl)
  let initialized := runOps rom (setWorkspace 1 0) state
  have is := piece_safe q full containing start hbound hcode .initialize state
    (by simpa only [RawCandidateRetentionWordChunks.chunkOffset, Nat.add_zero] using hpc) ha hf
    ⟨hptr, True.intro⟩ hend
  have runInit : natRun rom containing 6 state = initialized :=
    piece_run q full containing start hbound hcode .initialize state
      (by simpa only [RawCandidateRetentionWordChunks.chunkOffset, Nat.add_zero] using hpc) ha
  have ih : initialized.heap = Function.update state.heap (B + 1) 0 := by
    simpa only [hptr] using setWorkspace_heap rom 1 0 state
  have ib : initialized.heap 8 = B := by
    rw [ih]
    simpa only [Function.update_of_ne (by omega : 8 ≠ B + 1)] using hptr
  have im : initialized.heap B = M := by
    rw [ih]
    simpa only [Function.update_of_ne (by omega : B ≠ B + 1)] using hheader
  have ii : initialized.heap (B + 1) = 0 := by rw [ih]; simp
  have ip : initialized.pc = 5 * (start + 6) := by
    rw [show initialized = runOps rom (setWorkspace 1 0) state from rfl,
      runOps_pc rom (setWorkspace 1 0) state (by simp [setWorkspace, storeWorkspace, loadCell, NoJump]),
      setWorkspace_length, hpc]
    omega
  have ia : initialized.halted = false := (runOps_halted _ _ _).trans ha
  have initFits : RegistersFit (indexWidth 32 full.length q) initialized := by
    have hh := is.2
    change RegistersFit _ (natRun rom containing 6 state) at hh
    rwa [runInit] at hh
  have ss := outer_scan_partial_safe q full containing start hbound hcode initialized ib im ii ip ia initFits hend M le_rfl
  have sn := outer_scan_partial q full containing start hbound hcode B hb initialized ib im ii ip ia M le_rfl
  dsimp only at sn
  obtain ⟨si, _arrays, frame, sp, sa⟩ := sn
  let previous := natRun rom containing (outerScanSteps full.length q M) initialized
  have pb : previous.heap 8 = B :=
    (frame 8 ⟨le_rfl, by omega, by omega, by omega, Or.inl (by omega)⟩).trans ib
  have pm : previous.heap B = M :=
    (frame B ⟨by omega, by omega, by omega, by omega, Or.inl (by omega)⟩).trans im
  have ts := piece_safe q full containing start hbound hcode .outerTest previous sp sa ss.2
    ⟨pb, pm, si.le⟩ hend
  have bodySafe : PrefixSafe (SafePoint q full containing start) rom containing initialized
      (outerScanSteps full.length q M + 13) := PrefixSafe.add _ _ _ _ _ _ ss.1 ts.1
  have allSafe : PrefixSafe (SafePoint q full containing start) rom containing state
      (6 + (outerScanSteps full.length q M + 13)) := by
    apply PrefixSafe.add _ _ _ _ _ _ is.1
    change PrefixSafe (SafePoint q full containing start) rom containing
      (natRun rom containing 6 state) (outerScanSteps full.length q M + 13)
    rwa [runInit]
  have endFits : RegistersFit (indexWidth 32 full.length q)
      (natRun rom containing (totalSteps full.length q) state) := by
    rw [show totalSteps full.length q = 6 + (outerScanSteps full.length q M + 13) by
      dsimp [totalSteps, M]; omega,
      natRun_add, runInit, natRun_add]
    exact ts.2
  have rn := retention q full containing start hbound hcode B hb state hptr hheader hpc ha
  dsimp only at rn
  dsimp only
  refine ⟨?_, endFits, rn.1, rn.2.1, rn.2.2.2.2.2.1, rn.2.2.2.2.2.2⟩
  simpa only [totalSteps, M, Nat.add_assoc] using allSafe

theorem natRun_prefix_safe (state : NatState)
    (hptr : state.heap 8 = 16) (hheader : state.heap 16 = full.length + q + 1)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hfit : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398)))
    (count : Nat) (hc : count ≤ totalSteps full.length q) :
    RegistersFit (indexWidth 32 full.length q) (natRun (rawIncidenceROM q full) containing count state) ∧
      Fits (indexWidth 32 full.length q) (natRun (rawIncidenceROM q full) containing count state).pc ∧
      (natRun (rawIncidenceROM q full) containing count state).halted = false := by
  have safe := retention_nat_safe q full containing start hbound hcode state hptr hheader hpc ha hfit hend
  by_cases final : count = totalSteps full.length q
  · subst count
    refine ⟨safe.2.1, ?_, safe.2.2.2.2.2⟩
    rw [safe.2.2.2.2.1]
    exact hend
  · have point := safe.1 count (by omega)
    have fits := point_pcFits point hend
    have registers := point.1
    obtain ⟨_offset, _bound, _pc, active, _⟩ := point.2
    exact ⟨registers, fits, active⟩

omit hbound hcode in
private theorem input_prefix (initialUsed : Finset (Fin q)) :
    PA06A19PrepareROM001.ROMPrefix (rawIncidenceROM q full)
      (CompactControllerClaims.controllerInput q full initialUsed) :=
  PA06A19PrepareROM001.inputTail_prefix _
    ((List.finRange q).map (fun tool => bit (decide (tool ∈ initialUsed))))

/-- Real Word retention on the actual tail-bearing controllerInput, with
all numerical/access hypotheses established by the executing pieces. -/
theorem word_run_eq_nat (initialUsed : Finset (Fin q)) (state : NatState)
    (hptr : state.heap 8 = 16) (hheader : state.heap 16 = full.length + q + 1)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hfit : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398)))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ totalSteps full.length q) :
    packingRun (CompactControllerClaims.controllerInput q full initialUsed) containing count
      (state.toWord (indexWidth 32 full.length q)) =
        (natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 32 full.length q) := by
  have safe := retention_nat_safe q full containing start hbound hcode state hptr hheader hpc ha hfit hend
  have rawEq (k : Nat) (hk : k ≤ totalSteps full.length q) :
      natRun (CompactControllerClaims.controllerInput q full initialUsed) containing k state =
        natRun (rawIncidenceROM q full) containing k state := by
    apply PA06A19PrepareROM001.natRun_eq_of_romPrefix (input_prefix q full initialUsed)
      (PA06A19PrepareCompactWord008.linearLimit full.length q)
    intro clock hclock _active op hd
    obtain ⟨_fits, _offset, _bound, _pc, _active, actualOp, decoded, access⟩ := safe.1 clock (by omega)
    have heq : op = actualOp := Option.some.inj (hd.symm.trans decoded)
    subst op
    exact access
  have actual := natRun_toWord (CompactControllerClaims.controllerInput q full initialUsed) containing state count hwords (by
    intro k hk
    rw [rawEq k (by omega)]
    have point := safe.1 k (by omega)
    exact ⟨point.1, point_pcFits point hend⟩)
  exact actual.trans (congrArg (NatState.toWord (indexWidth 32 full.length q)) (rawEq count hc))

theorem word_prefix_safe (initialUsed : Finset (Fin q)) (state : NatState)
    (hptr : state.heap 8 = 16) (hheader : state.heap 16 = full.length + q + 1)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hfit : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 398)))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode containing))
    (count : Nat) (hc : count < totalSteps full.length q) :
    let runtime := CompactControllerClaims.controllerInput q full initialUsed
    let actual := packingRun runtime containing count (state.toWord (indexWidth 32 full.length q))
    actual.halted = false ∧ actual.pc.toNat + 4 < (packingCode containing).length ∧
      ∃ op, PackingOp.decode (fetch containing actual) = some op ∧
        packingAccessFits runtime (PA06A19PrepareCompactWord008.linearLimit full.length q) actual op := by
  have safe := retention_nat_safe q full containing start hbound hcode state hptr hheader hpc ha hfit hend
  have point := safe.1 count hc
  have pcFit := point_pcFits point hend
  obtain ⟨registers, offset, hoff, pc, active, op, decoded, access⟩ := point
  dsimp only
  rw [word_run_eq_nat q full containing start hbound hcode initialUsed state hptr hheader hpc ha hfit hend hwords count hc.le]
  have pcWord : ((natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 32 full.length q)).pc.toNat =
      5 * (start + offset) := by
    change (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit, pc]
  refine ⟨active, ?_, op, ?_, ?_⟩
  · rw [pcWord, packingCode_length]
    omega
  · change PackingOp.decode (physicalFetch _ (packingCode containing)
      ((natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 32 full.length q)).pc.toNat) = _
    rw [pcWord, physicalFetch_eq _ _ _ hwords]
    change PackingOp.decode (natFetch containing (5 * (start + offset))) = some op
    simpa only [pc] using decoded
  · apply physical_access_of_nat (CompactControllerClaims.controllerInput q full initialUsed)
      (PA06A19PrepareCompactWord008.linearLimit full.length q) _ _ registers
    cases op with
    | base instruction =>
      exact PA06A19PrepareROM001.accessFits_of_romPrefix (input_prefix q full initialUsed)
        (PA06A19PrepareCompactWord008.linearLimit full.length q) _ instruction
        (by simpa only [RawIncidenceScanSafety.NatAccessFits,
          PA06A19PrepareCompactRetention020Args.linearLimit] using access)
    | arithmetic operation target left right => trivial
    | jumpIfZero condition target => trivial

/-- The original retained-card/keep semantics, on the very same encoded
raw run used by the Word refinement and prefix-safety theorems above. -/
theorem retention_native_output (state : NatState)
    (hptr : state.heap 8 = 16) (hheader : state.heap 16 = full.length + q + 1)
    (hpc : state.pc = 5 * start) (ha : state.halted = false) :
    let actual := natRun (rawIncidenceROM q full) containing (totalSteps full.length q) state
    actual.heap 8 = 16 ∧ actual.heap 16 = full.length + q + 1 ∧ actual.heap 17 = full.length + q + 1 ∧
      (∀ index < full.length + q + 1,
        actual.heap (cardAddress 16 index) = ((RawCandidateOrder.candidateSupports q full).getD index ∅).card ∧
        actual.heap (keepAddress 16 (full.length + q + 1) index) = bit (RawCandidateOrder.keepCandidate q full index)) ∧
      (∀ address, OutsideWorkspace 16 (full.length + q + 1) address → actual.heap address = state.heap address) ∧
      actual.pc = 5 * (start + 398) ∧ actual.halted = false :=
  retention q full containing start hbound hcode 16 (by decide) state hptr hheader hpc ha

end Linked

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention030Loop


