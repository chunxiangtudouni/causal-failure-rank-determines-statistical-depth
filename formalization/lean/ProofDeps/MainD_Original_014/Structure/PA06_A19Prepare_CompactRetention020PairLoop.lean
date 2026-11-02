module

public import Structure.PA06_A19Prepare_CompactRetention020PairKernel

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Compact PairScan proof COMPOSITION. This reuses the original Nat
iteration/scan/frame theorems and exact step counts. Width32 short-piece
and raw-kernel certificates from020/015 replace the old width16/distant
workspace certificates. Source-cell needs at each executed boundary are
actually established below; no whole-run safety is a caller premise.
No Nat loop implementation or correctness theorem is rebuilt. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention020PairLoop

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open RawCandidatePairScan (programAt initBlock leftArguments rightArguments)
open RawCandidatePairScanWord (Chunk chunkOffset chunk_run witness_sums_le)
open PA06A19PrepareCompactRetention020 (SafePoint chunk_safe)
open PA06A19PrepareCompactRetention020PairKernel (kernel_safe)

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 125 ≤ containing.length)
  (hcode : ∀ position < 125, containing.getD (start + position) RawCandidatePairScanWord.paddingOp =
    (programAt start).getD position RawCandidatePairScanWord.paddingOp)

include hbound hcode

theorem iteration_safe (left right : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 5 * (start + 16)) (ha : state.halted = false)
    (hq : state.heap 0 = q) (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (ht : state.heap 3 = tool.val) (h4 : state.heap 4 ≤ tool.val) (h5 : state.heap 5 ≤ tool.val) (h6 : state.heap 6 ≤ tool.val)
    (hfit : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 125))) :
    let count := RawCandidatePairScan.iterationSteps full.length left.val right.val tool.val
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state count ∧
      RegistersFit (indexWidth 32 full.length q) (natRun (rawIncidenceROM q full) containing count state) := by
  let rom := rawIncidenceROM q full
  let s0 := runOps rom (testCell 0 3 (start + 125)) state
  have tr := runOps_testCell rom 0 3 (start + 125) state
  have th : s0.heap = state.heap := tr.1
  have tp : s0.pc = 5 * (start + 23) := by
    have hp := tr.2.2.1
    rw [hq, ht, ite_eq_right (Nat.sub_ne_zero_of_lt tool.isLt), hpc] at hp
    dsimp only [s0]
    omega
  have ta : s0.halted = false := tr.2.2.2.trans ha
  have ts := chunk_safe q full containing start hbound hcode .test state hpc ha hfit
    ⟨hq.le, by rw [ht]; exact tool.isLt.le⟩ hend
  rw [chunk_run q full containing start hbound hcode .test state hpc ha] at ts
  let s1 := runOps rom leftArguments s0
  have p1 : s1.pc = 5 * (start + 27) := by
    rw [show s1 = runOps _ _ _ from rfl, runOps_pc _ _ _ (by simp [leftArguments, loadCell, NoJump]), tp]
    change 5 * (start + 23) + 5 * 4 = _
    omega
  have a1 : s1.halted = false := (runOps_halted _ _ _).trans ta
  have h1 : s1.heap = state.heap := by simpa [s1, leftArguments, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute] using th
  have old1 : s1.register .old = left.val := by
    simpa [s1, leftArguments, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, th] using hl
  have fresh1 : s1.register .fresh = tool.val := by
    simpa [s1, leftArguments, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, th] using ht
  have as1 := chunk_safe q full containing start hbound hcode .leftArgs s0 tp ta ts.2
    ⟨by rw [th, hl]; exact left.isLt, by rw [th, ht]; exact tool.isLt.le⟩ hend
  rw [chunk_run q full containing start hbound hcode .leftArgs s0 tp ta] at as1
  let ls := RawCandidateIncidenceWord.steps full.length left.val tool.val
  let rs := RawCandidateIncidenceWord.steps full.length right.val tool.val
  let s2 := natRun rom containing ls s1
  have lk := kernel_safe q full containing start hbound hcode 27 (Or.inl rfl) left tool s1 p1 a1 as1.2 hend old1 fresh1
  dsimp only at lk
  have lkReturn := lk.2.2
  have hv2 : s2.register .value = RawCandidatePairScan.candidateBit full left tool.val := by
    simpa only [RawCandidatePairScan.candidateBit_fin] using lkReturn.1
  have h2 : s2.heap = state.heap := lkReturn.2.2.2.1.trans h1
  have p2 : s2.pc = 5 * (start + 59) := by have h := lkReturn.2.2.2.2.1; dsimp only [s2]; omega
  have a2 : s2.halted = false := lkReturn.2.2.2.2.2
  let s3 := runOps rom rightArguments s2
  have p3 : s3.pc = 5 * (start + 65) := by
    rw [show s3 = runOps _ _ _ from rfl, runOps_pc _ _ _ (by simp [rightArguments, loadCell, storeCell, NoJump]), p2]
    change 5 * (start + 59) + 5 * 6 = _
    omega
  have a3 : s3.halted = false := (runOps_halted _ _ _).trans a2
  have h3 : s3.heap = Function.update state.heap 7 (RawCandidatePairScan.candidateBit full left tool.val) := by
    simp [s3, rightArguments, loadCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, h2, hv2]
  have old3 : s3.register .old = right.val := by
    simpa [s3, rightArguments, loadCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, h2] using hr
  have fresh3 : s3.register .fresh = tool.val := by
    simpa [s3, rightArguments, loadCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, h2] using ht
  have as3 := chunk_safe q full containing start hbound hcode .rightArgs s2 p2 a2 lk.2.1
    ⟨by rw [h2, hr]; exact right.isLt, by rw [h2, ht]; exact tool.isLt.le⟩ hend
  rw [chunk_run q full containing start hbound hcode .rightArgs s2 p2 a2] at as3
  let s4 := natRun rom containing rs s3
  have rk := kernel_safe q full containing start hbound hcode 65 (Or.inr rfl) right tool s3 p3 a3 as3.2 hend old3 fresh3
  dsimp only at rk
  have rkReturn := rk.2.2
  have hv4 : s4.register .value = RawCandidatePairScan.candidateBit full right tool.val := by
    simpa only [RawCandidatePairScan.candidateBit_fin] using rkReturn.1
  have h4heap : s4.heap = Function.update state.heap 7 (RawCandidatePairScan.candidateBit full left tool.val) := rkReturn.2.2.2.1.trans h3
  have p4 : s4.pc = 5 * (start + 97) := by have h := rkReturn.2.2.2.2.1; dsimp only [s4]; omega
  have a4 : s4.halted = false := rkReturn.2.2.2.2.2
  have hbit (candidate : Fin (full.length + q + 1)) : RawCandidatePairScan.candidateBit full candidate tool.val ≤ 1 := by
    rw [RawCandidatePairScan.candidateBit_fin]
    simp only [bit]
    split <;> omega
  have needs : PA06A19PrepareCompactRetention020.Needs q full .update s4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [h4heap, Function.update_of_ne (by decide : (3 : Nat) ≠ 7), ht] using tool.isLt
    · simpa only [h4heap, Function.update_of_ne (by decide : (4 : Nat) ≠ 7),
        Function.update_of_ne (by decide : (3 : Nat) ≠ 7), ht] using h4
    · simpa only [h4heap, Function.update_of_ne (by decide : (5 : Nat) ≠ 7),
        Function.update_of_ne (by decide : (3 : Nat) ≠ 7), ht] using h5
    · simpa only [h4heap, Function.update_of_ne (by decide : (6 : Nat) ≠ 7),
        Function.update_of_ne (by decide : (3 : Nat) ≠ 7), ht] using h6
    · simpa only [h4heap, Function.update_self] using hbit left
    · simpa only [hv4] using hbit right
  have us := chunk_safe q full containing start hbound hcode .update s4 p4 a4 rk.2.1 needs hend
  have runTest : natRun (rawIncidenceROM q full) containing 7 state = s0 :=
    chunk_run q full containing start hbound hcode .test state hpc ha
  have runLeft : natRun (rawIncidenceROM q full) containing 4 s0 = s1 :=
    chunk_run q full containing start hbound hcode .leftArgs s0 tp ta
  have runRight : natRun (rawIncidenceROM q full) containing 6 s2 = s3 :=
    chunk_run q full containing start hbound hcode .rightArgs s2 p2 a2
  have sp4 : PrefixSafe (SafePoint q full containing start) rom containing s3 (rs + 28) :=
    PrefixSafe.add _ _ _ _ rs 28 rk.1 us.1
  have sp3 : PrefixSafe (SafePoint q full containing start) rom containing s2 (6 + (rs + 28)) := by
    apply PrefixSafe.add _ _ _ _ 6 (rs + 28) as3.1
    rw [runRight]
    exact sp4
  have sp2 : PrefixSafe (SafePoint q full containing start) rom containing s1 (ls + (6 + (rs + 28))) :=
    PrefixSafe.add _ _ _ _ ls _ lk.1 sp3
  have sp1 : PrefixSafe (SafePoint q full containing start) rom containing s0 (4 + (ls + (6 + (rs + 28)))) := by
    apply PrefixSafe.add _ _ _ _ 4 _ as1.1
    rw [runLeft]
    exact sp2
  have sp0 : PrefixSafe (SafePoint q full containing start) rom containing state (7 + (4 + (ls + (6 + (rs + 28))))) := by
    apply PrefixSafe.add _ _ _ _ 7 _ ts.1
    rw [runTest]
    exact sp1
  have hsteps : RawCandidatePairScan.iterationSteps full.length left.val right.val tool.val =
      7 + (4 + (ls + (6 + (rs + 28)))) := by
    dsimp only [RawCandidatePairScan.iterationSteps, ls, rs, RawCandidateIncidenceWord.steps]
    omega
  refine ⟨by simpa only [hsteps] using sp0, ?_⟩
  rw [hsteps, natRun_add, runTest]
  change RegistersFit _ (natRun rom containing (4 + (ls + (6 + (rs + 28)))) s0)
  rw [natRun_add, runLeft, natRun_add]
  change RegistersFit _ (natRun rom containing (6 + (rs + 28)) s2)
  rw [natRun_add, runRight, natRun_add]
  exact us.2

theorem scan_partial_safe (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * (start + 16)) (ha : state.halted = false)
    (hq : state.heap 0 = q) (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (h3 : state.heap 3 = 0) (h4 : state.heap 4 = 0) (h5 : state.heap 5 = 0) (h6 : state.heap 6 = 0)
    (hfit : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 125)))
    (count : Nat) (hc : count ≤ q) :
    let clock := RawCandidatePairScan.scanSteps full.length left.val right.val count
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state clock ∧
      RegistersFit (indexWidth 32 full.length q) (natRun (rawIncidenceROM q full) containing clock state) := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [RawCandidatePairScan.scanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 0 ∧
        RegistersFit (indexWidth 32 full.length q) state from ⟨by intro clock hk; omega, hfit⟩)
  | succ count ih =>
    intro hc
    rcases ih (by omega) with ⟨safe, fits⟩
    let previous := natRun (rawIncidenceROM q full) containing (RawCandidatePairScan.scanSteps full.length left.val right.val count) state
    have hs := RawCandidatePairScan.scan_partial q full containing start hbound hcode left right state hpc ha hq hl hr h3 count (by omega)
    dsimp only at hs
    rcases hs with ⟨cursor, inter, leftOnly, rightOnly, frame, pointer, active⟩
    have hq' : previous.heap 0 = q := (frame 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hq
    have hl' : previous.heap 1 = left.val := (frame 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl
    have hr' : previous.heap 2 = right.val := (frame 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr
    rw [h4, Nat.zero_add] at inter
    rw [h5, Nat.zero_add] at leftOnly
    rw [h6, Nat.zero_add] at rightOnly
    have hb := witness_sums_le full left right count
    have hi := iteration_safe q full containing start hbound hcode left right ⟨count, by omega⟩ previous pointer active
      hq' hl' hr' cursor (inter.le.trans hb.1) (leftOnly.le.trans hb.2.1) (rightOnly.le.trans hb.2.2) fits hend
    dsimp only at hi
    refine ⟨?_, ?_⟩
    · rw [RawCandidatePairScan.scanSteps_succ]
      exact PrefixSafe.add _ _ _ _ _ _ safe hi.1
    · rw [RawCandidatePairScan.scanSteps_succ, natRun_add]
      exact hi.2

theorem scan_nat_safe (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hfit : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 125))) :
    let clock := RawCandidatePairScan.totalSteps full.length left.val right.val q
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state clock ∧
      RegistersFit (indexWidth 32 full.length q) (natRun (rawIncidenceROM q full) containing clock state) := by
  let rom := rawIncidenceROM q full
  let initialized := runOps rom initBlock state
  have hip : state.pc = 5 * (start + chunkOffset .init) := by simpa only [chunkOffset, Nat.add_zero] using hpc
  have his := chunk_safe q full containing start hbound hcode .init state hip ha hfit True.intro hend
  rw [chunk_run q full containing start hbound hcode .init state hip ha] at his
  have hi : initialized.heap 0 = q ∧ initialized.heap 3 = 0 ∧ initialized.heap 4 = 0 ∧
      initialized.heap 5 = 0 ∧ initialized.heap 6 = 0 ∧
      (∀ address, address ≠ 0 → address ≠ 3 → address ≠ 4 → address ≠ 5 → address ≠ 6 →
        initialized.heap address = state.heap address) := by
    simp [initialized, initBlock, setCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, rom, raw_header_q]
    intro address h0 h3 h4 h5 h6
    simp [h0, h3, h4, h5, h6]
  have p0 : initialized.pc = 5 * (start + 16) := by
    rw [show initialized = runOps _ _ _ from rfl, runOps_pc _ _ _ (by simp [initBlock, setCell, storeCell, NoJump]), hpc]
    change 5 * start + 5 * 16 = _
    omega
  have a0 : initialized.halted = false := (runOps_halted _ _ _).trans ha
  have il : initialized.heap 1 = left.val := (hi.2.2.2.2.2 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl
  have ir : initialized.heap 2 = right.val := (hi.2.2.2.2.2 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr
  have ss := scan_partial_safe q full containing start hbound hcode left right initialized p0 a0 hi.1 il ir
    hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 his.2 hend q le_rfl
  let clock := RawCandidatePairScan.scanSteps full.length left.val right.val q
  let previous := natRun rom containing clock initialized
  have sem := RawCandidatePairScan.scan_partial q full containing start hbound hcode left right initialized
    p0 a0 hi.1 il ir hi.2.1 q le_rfl
  dsimp only at sem
  rcases sem with ⟨cursor, _inter, _leftOnly, _rightOnly, frame, pointer, active⟩
  have pq : previous.heap 0 = q := (frame 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi.1
  have ts := chunk_safe q full containing start hbound hcode .test previous pointer active ss.2
    ⟨pq.le, cursor.le⟩ hend
  have ps : PrefixSafe (SafePoint q full containing start) rom containing initialized (clock + 7) :=
    PrefixSafe.add _ _ _ _ clock 7 ss.1 ts.1
  have runInit : natRun (rawIncidenceROM q full) containing 16 state = initialized :=
    chunk_run q full containing start hbound hcode .init state hip ha
  have allSafe : PrefixSafe (SafePoint q full containing start) rom containing state (16 + (clock + 7)) := by
    apply PrefixSafe.add _ _ _ _ 16 _ his.1
    rw [runInit]
    exact ps
  have hsteps : RawCandidatePairScan.totalSteps full.length left.val right.val q = 16 + (clock + 7) := by
    dsimp only [RawCandidatePairScan.totalSteps, clock]
    omega
  refine ⟨by simpa only [hsteps] using allSafe, ?_⟩
  rw [hsteps, natRun_add, runInit, natRun_add]
  exact ts.2

theorem natRun_prefix_safe (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hfit : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 125)))
    (count : Nat) (hc : count ≤ RawCandidatePairScan.totalSteps full.length left.val right.val q) :
    RegistersFit (indexWidth 32 full.length q) (natRun (rawIncidenceROM q full) containing count state) ∧
      Fits (indexWidth 32 full.length q) (natRun (rawIncidenceROM q full) containing count state).pc ∧
      (natRun (rawIncidenceROM q full) containing count state).halted = false := by
  have hs := scan_nat_safe q full containing start hbound hcode left right state hpc ha hl hr hfit hend
  by_cases heq : count = RawCandidatePairScan.totalSteps full.length left.val right.val q
  · subst count
    have hn := RawCandidatePairScan.scan q full containing start hbound hcode left right state hpc ha hl hr
    dsimp only at hn
    exact ⟨hs.2, lt_of_le_of_lt hn.2.2.2.2.2.2.1.le hend, hn.2.2.2.2.2.2.2⟩
  · have hp := hs.1 count (by omega)
    rcases hp.2 with ⟨offset, hoff, hpc', active, _⟩
    exact ⟨hp.1, lt_of_le_of_lt (by rw [hpc']; omega) hend, active⟩

omit hbound hcode in
private theorem input_prefix (initialUsed : Finset (Fin q)) :
    PA06A19PrepareROM001.ROMPrefix (rawIncidenceROM q full)
      (CompactControllerClaims.controllerInput q full initialUsed) :=
  PA06A19PrepareROM001.inputTail_prefix _
    ((List.finRange q).map (fun tool => bit (decide (tool ∈ initialUsed))))

/-- Actual Word scan prefixes at full width32 on the original controller
input. The previous scalar/kernel pieces discharge safety, rather than
providing it as a caller assumption. -/
theorem word_run_eq_nat (initialUsed : Finset (Fin q)) (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hfit : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 125)))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ RawCandidatePairScan.totalSteps full.length left.val right.val q) :
    packingRun (CompactControllerClaims.controllerInput q full initialUsed) containing count
      (state.toWord (indexWidth 32 full.length q)) =
        (natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 32 full.length q) := by
  have safe := scan_nat_safe q full containing start hbound hcode left right state hpc ha hl hr hfit hend
  have rawEq (k : Nat) (hk : k ≤ RawCandidatePairScan.totalSteps full.length left.val right.val q) :
      natRun (CompactControllerClaims.controllerInput q full initialUsed) containing k state =
        natRun (rawIncidenceROM q full) containing k state := by
    apply PA06A19PrepareROM001.natRun_eq_of_romPrefix (input_prefix q full initialUsed) 8
    intro clock hclock _active op hd
    obtain ⟨_fits, _offset, _bound, _pc, _active, actualOp, decoded, access⟩ := safe.1 clock (by omega)
    have heq : op = actualOp := Option.some.inj (hd.symm.trans decoded)
    subst op
    exact access
  have actual := natRun_toWord (CompactControllerClaims.controllerInput q full initialUsed) containing state count hwords (by
    intro k hk
    rw [rawEq k (by omega)]
    have point := safe.1 k (by omega)
    exact ⟨point.1, point.pcFits hend⟩)
  exact actual.trans (congrArg (NatState.toWord (indexWidth 32 full.length q)) (rawEq count hc))

/-- All actual physical accesses of the full dynamic PairScan remain
within its eight scratch words, with fetched code and active PC proved. -/
theorem word_prefix_safe (initialUsed : Finset (Fin q)) (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hfit : RegistersFit (indexWidth 32 full.length q) state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 125)))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode containing))
    (count : Nat) (hc : count < RawCandidatePairScan.totalSteps full.length left.val right.val q) :
    let runtime := CompactControllerClaims.controllerInput q full initialUsed
    let actual := packingRun runtime containing count (state.toWord (indexWidth 32 full.length q))
    actual.halted = false ∧ actual.pc.toNat + 4 < (packingCode containing).length ∧
      ∃ op, PackingOp.decode (fetch containing actual) = some op ∧ packingAccessFits runtime 8 actual op := by
  have safe := scan_nat_safe q full containing start hbound hcode left right state hpc ha hl hr hfit hend
  have point := safe.1 count hc
  have pcFit := point.pcFits hend
  obtain ⟨registers, offset, hoff, pc, active, op, decoded, access⟩ := point
  dsimp only
  rw [word_run_eq_nat q full containing start hbound hcode initialUsed left right state hpc ha hl hr hfit hend hwords count hc.le]
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
  · apply physical_access_of_nat (CompactControllerClaims.controllerInput q full initialUsed) 8 _ _ registers
    cases op with
    | base instruction =>
      exact PA06A19PrepareROM001.accessFits_of_romPrefix (input_prefix q full initialUsed) 8 _ instruction
        (by simpa only [NatAccessFits] using access)
    | arithmetic operation target left right => trivial
    | jumpIfZero condition target => trivial

end Linked

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention020PairLoop


