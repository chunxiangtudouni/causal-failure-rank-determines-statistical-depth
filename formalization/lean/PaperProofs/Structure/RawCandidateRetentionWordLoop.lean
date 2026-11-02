module

public import PaperProofs.Structure.RawCandidateRetentionWordCard
public import PaperProofs.Structure.RawCandidateRetentionWordInner

/-! Safety of the whole actual dynamic retention loop.  The only runtime
workspace inputs are its pointer and count header.  Scratch cells and all
cardinality/keep values are established by the executed program. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateRetentionWordLoop

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateRetentionRAM
open RawCandidateWorkspaceInit (workspaceBase candidateCount workspaceBase_ge)
open RawCandidateRetentionWordSafety (SafePoint)
open RawCandidateRetentionWordPieces (piece_safe piece_run)

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 398 ≤ containing.length)
  (hcode : ∀ position < 398, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem outer_iteration_safe (index : Nat) (hi : index < candidateCount full.length q)
    (state : NatState) (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hindex : state.heap (workspaceBase full.length q + 1) = index)
    (hpc : state.pc = 5 * (start + 6)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 398))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
      (outerIterationSteps full.length q index) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (outerIterationSteps full.length q index) state) := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  have hb : 16 ≤ B := workspaceBase_ge full.length q
  let seeded := natRun rom containing (cardPhaseSteps full.length q index) state
  have cs := RawCandidateRetentionWordCard.card_phase_safe q full containing start hbound hcode
    index hi state hptr hheader hindex hpc ha hf hend
  have cn := card_phase q full containing start hbound hcode B index hb hi state hptr hheader hindex hpc ha
  dsimp only at cn
  rcases cn with ⟨cj, cf, cr, _card, frame, cp, ca⟩
  have cb : seeded.heap 8 = B :=
    (frame 8 le_rfl (by omega) (by omega) (by unfold cardAddress; omega)).trans hptr
  have cm : seeded.heap B = candidateCount full.length q :=
    (frame B (by omega) (by omega) (by omega) (by unfold cardAddress; omega)).trans hheader
  have ci : seeded.heap (B + 1) = index :=
    (frame (B + 1) (by omega) (by omega) (by omega) (by unfold cardAddress; omega)).trans hindex
  have cfle : seeded.heap (B + 3) ≤ 1 := by
    rw [cf]
    simp only [RawCandidateRetentionFlags.partialFlag, bit]
    split <;> omega
  have ready : RawCandidateRetentionWordInner.Ready q full index (index + 1) (5 * (start + 180)) seeded :=
    ⟨cb, cm, ci, cj, cfle, cp, ca⟩
  have ins := RawCandidateRetentionWordInner.inner_scan_safe q full containing start hbound hcode
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
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hindex : state.heap (workspaceBase full.length q + 1) = 0)
    (hpc : state.pc = 5 * (start + 6)) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 398)))
    (count : Nat) (hc : count ≤ candidateCount full.length q) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
      (outerScanSteps full.length q count) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (outerScanSteps full.length q count) state) := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [outerScanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 0 ∧
        RegistersFit (indexWidth 16 full.length q) state from ⟨by intro clock hclock; omega, hf⟩)
  | succ count ih =>
    intro hc
    obtain ⟨safe, fits⟩ := ih (by omega)
    let B := workspaceBase full.length q
    have hb : 16 ≤ B := workspaceBase_ge full.length q
    let previous := natRun (rawIncidenceROM q full) containing (outerScanSteps full.length q count) state
    have pn := outer_scan_partial q full containing start hbound hcode B hb state hptr hheader hindex hpc ha
      count ((Nat.le_succ count).trans hc)
    dsimp only at pn
    obtain ⟨pi, _arrays, frame, pp, pa⟩ := pn
    have pb : previous.heap 8 = B :=
      (frame 8 ⟨le_rfl, by omega, by omega, by omega, Or.inl (by omega)⟩).trans hptr
    have pm : previous.heap B = candidateCount full.length q :=
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
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 398))) :
    let result := natRun (rawIncidenceROM q full) containing (totalSteps full.length q) state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
      (totalSteps full.length q) ∧ RegistersFit (indexWidth 16 full.length q) result ∧
      result.heap 8 = workspaceBase full.length q ∧
      result.heap (workspaceBase full.length q) = candidateCount full.length q ∧
      result.pc = 5 * (start + 398) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  have hb : 16 ≤ B := workspaceBase_ge full.length q
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
  have initFits : RegistersFit (indexWidth 16 full.length q) initialized := by
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
  have endFits : RegistersFit (indexWidth 16 full.length q)
      (natRun rom containing (totalSteps full.length q) state) := by
    rw [show totalSteps full.length q = 6 + (outerScanSteps full.length q M + 13) by
      dsimp [totalSteps, M, candidateCount]; omega,
      natRun_add, runInit, natRun_add]
    exact ts.2
  have rn := retention q full containing start hbound hcode B hb state hptr hheader hpc ha
  dsimp only at rn
  dsimp only
  refine ⟨?_, endFits, rn.1, rn.2.1, rn.2.2.2.2.2.1, rn.2.2.2.2.2.2⟩
  simpa only [totalSteps, M, candidateCount, Nat.add_assoc] using allSafe

end Linked

end PaperProofs.Structure.LaminarTree.RawCandidateRetentionWordLoop
