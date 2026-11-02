module

public import Structure.PA06_A19Prepare_InitialUsed037_Loop
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate final assembly: the real33-op setup establishes the concrete
j=0 invariant, then the existing actual Word loop runs q iterations. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PSTRBuildLower
open AlgorithmClaims.PackedCapacityRAM

/- Keep update lookup reductions on abstract words. In the caller, both
the actual33-op output and its three keys are already fixed by hheap. -/
private theorem update3_values {wordBits : Nat}
    (heap : BitVec wordBits → BitVec wordBits)
    (pointer cursor counter pointerValue cursorValue counterValue : BitVec wordBits)
    (hpc : pointer ≠ cursor) (hpt : pointer ≠ counter) (hct : cursor ≠ counter) :
    let fresh := Function.update (Function.update (Function.update heap pointer pointerValue)
      cursor cursorValue) counter counterValue
    fresh pointer = pointerValue ∧ fresh cursor = cursorValue ∧ fresh counter = counterValue := by
  dsimp only
  constructor
  · rw [Function.update_of_ne hpt, Function.update_of_ne hpc, Function.update_self]
  · constructor
    · rw [Function.update_of_ne hct, Function.update_self]
    · exact Function.update_self _ _ _

theorem setup_physical_heap (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false) (hd : BankData q full before)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ setup ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ setup ++ right).length)) :
    (packingRun (controllerInput q full used) (left ++ setup ++ right) 33 before).heap =
      Function.update (Function.update (Function.update before.heap
        (before.register .address + BitVec.ofNat _ pointerSlot) (BitVec.ofNat _ (tableWords full.length q (treeSize q full))))
        (before.register .address + BitVec.ofNat _ cursorSlot) (BitVec.ofNat _ (2 + full.length * q)))
        (before.register .address + BitVec.ofNat _ counterSlot) (BitVec.ofNat _ q) := by
  let bits := indexWidth 32 full.length q
  let natural := PA06A19PrepareRuntimeHeader019.natView before
  let CB := (before.register .address).toNat
  have hdata := bank_natView q full before hd
  have hheap := setup_heap q full used hq natural CB rfl hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2
  have hf16 : Fits bits (CB + pointerSlot) := by
    dsimp only [CB, bits]
    rw [hd.base]
    exact (actual_control_room q full hq pointerSlot (by decide)).2
  have hf17 : Fits bits (CB + cursorSlot) := by
    dsimp only [CB, bits]
    rw [hd.base]
    exact (actual_control_room q full hq cursorSlot (by decide)).2
  have hf18 : Fits bits (CB + counterSlot) := by
    dsimp only [CB, bits]
    rw [hd.base]
    exact (actual_control_room q full hq counterSlot (by decide)).2
  have hOriginal : (fun point : BitVec bits => BitVec.ofNat bits (natural.heap point.toNat)) = before.heap := by
    dsimp only [bits, natural]
    exact congrArg (fun s : WordState (indexWidth 32 full.length q) => s.heap)
      (PA06A19PrepareRuntimeHeader019.natView_toWord before)
  rw [setup_word q full used hq left right before hpc ha hd hcode hpcCode]
  change (fun point : BitVec bits => BitVec.ofNat bits ((runOps _ setup natural).heap point.toNat)) = _
  rw [hheap,
    map_update_heap bits _ (CB + counterSlot) q hf18,
    map_update_heap bits _ (CB + cursorSlot) (2 + full.length * q) hf17,
    map_update_heap bits natural.heap (CB + pointerSlot) (tableWords full.length q (treeSize q full)) hf16,
    hOriginal]
  simp only [CB, bits, PA06A19PrepareBankPacked021.bankWord_eq]

theorem setup_current (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false) (hd : BankData q full before)
    (hh : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hbound : CapacityPrefixBounded q (capacityWords 8192 full.length q (treeSize q full))
      (unpackHeap q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) (dataHeap before.heap)))
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ setup ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ setup ++ right).length)) :
    Current q full used before 0 (packingRun (controllerInput q full used) (left ++ setup ++ right) 33 before) := by
  let bits := indexWidth 32 full.length q
  let t := treeSize q full
  let C := capacityWords 8192 full.length q t
  let P := packedCapacityWords q C bits
  let CB := (before.register .address).toNat
  let after := packingRun (controllerInput q full used) (left ++ setup ++ right) 33 before
  have hheap := setup_physical_heap q full used hq left right before hpc ha hd hcode hpcCode
  have hf16 : Fits bits (CB + pointerSlot) := by
    dsimp only [CB, bits]
    rw [hd.base]
    exact (actual_control_room q full hq pointerSlot (by decide)).2
  have hf17 : Fits bits (CB + cursorSlot) := by
    dsimp only [CB, bits]
    rw [hd.base]
    exact (actual_control_room q full hq cursorSlot (by decide)).2
  have hf18 : Fits bits (CB + counterSlot) := by
    dsimp only [CB, bits]
    rw [hd.base]
    exact (actual_control_room q full hq counterSlot (by decide)).2
  have hafter (slot : Nat) : 4 + P ≤ CB + slot := by
    have hp := actual_control_after_lookahead q full slot
    change 4 + P + 1 ≤ PA06A19PrepareControlBank017.controlBase full.length q t P + slot at hp
    rw [← hd.base] at hp
    dsimp only [CB]
    omega
  have hregion := PA06A19PrepareRuntimeLayout026.actual_product_fits q full hq
  rw [PA06A19PrepareRuntimeLayout026.capacityExpr_eq _ _ _ hq] at hregion
  have hcap (a : Nat) (haC : a < C) : scalar q full after.heap a = scalar q full before.heap a := by
    change unpackHeap q C bits (dataHeap after.heap) a = unpackHeap q C bits (dataHeap before.heap) a
    rw [hheap]
    simp only [PA06A19PrepareBankPacked021.bankWord_eq]
    rw [update_control_capacity q C (CB + counterSlot) _ _ (PA17PackingBounds043.bits_pos full.length q) hregion (hafter counterSlot) hf18 a haC,
      update_control_capacity q C (CB + cursorSlot) _ _ (PA17PackingBounds043.bits_pos full.length q) hregion (hafter cursorSlot) hf17 a haC,
      update_control_capacity q C (CB + pointerSlot) _ _ (PA17PackingBounds043.bits_pos full.length q) hregion (hafter pointerSlot) hf16 a haC]
  have hheader : PA06A19PrepareRuntimePacked016.Header q after.heap := by
    rw [hheap]
    simp only [PA06A19PrepareBankPacked021.bankWord_eq]
    apply PA06A19PrepareRuntimePacked016.update_header q _ _ _ _ (by have he := hafter counterSlot; omega) hf18
    apply PA06A19PrepareRuntimePacked016.update_header q _ _ _ _ (by have he := hafter cursorSlot; omega) hf17
    exact PA06A19PrepareRuntimePacked016.update_header q _ _ _ hh (by have he := hafter pointerSlot; omega) hf16
  have pointerAddress : before.register .address + BitVec.ofNat bits pointerSlot =
      BitVec.ofNat bits (CB + pointerSlot) :=
    PA06A19PrepareBankPacked021.bankWord_eq (before.register .address) pointerSlot
  have cursorAddress : before.register .address + BitVec.ofNat bits cursorSlot =
      BitVec.ofNat bits (CB + cursorSlot) :=
    PA06A19PrepareBankPacked021.bankWord_eq (before.register .address) cursorSlot
  have counterAddress : before.register .address + BitVec.ofNat bits counterSlot =
      BitVec.ofNat bits (CB + counterSlot) :=
    PA06A19PrepareBankPacked021.bankWord_eq (before.register .address) counterSlot
  have hne16_17 : before.register .address + BitVec.ofNat bits pointerSlot ≠ before.register .address + BitVec.ofNat bits cursorSlot := by
    rw [pointerAddress, cursorAddress]
    exact (ofNat_injective_of_fit _ _ hf16 hf17).not.mpr (by dsimp only [pointerSlot, cursorSlot]; omega)
  have hne16_18 : before.register .address + BitVec.ofNat bits pointerSlot ≠ before.register .address + BitVec.ofNat bits counterSlot := by
    rw [pointerAddress, counterAddress]
    exact (ofNat_injective_of_fit _ _ hf16 hf18).not.mpr (by dsimp only [pointerSlot, counterSlot]; omega)
  have hne17_18 : before.register .address + BitVec.ofNat bits cursorSlot ≠ before.register .address + BitVec.ofNat bits counterSlot := by
    rw [cursorAddress, counterAddress]
    exact (ofNat_injective_of_fit _ _ hf17 hf18).not.mpr (by dsimp only [cursorSlot, counterSlot]; omega)
  have hValues : after.heap (before.register .address + BitVec.ofNat bits pointerSlot) = BitVec.ofNat bits (tableWords full.length q t) ∧
      after.heap (before.register .address + BitVec.ofNat bits cursorSlot) = BitVec.ofNat bits (2 + full.length * q) ∧
      after.heap (before.register .address + BitVec.ofNat bits counterSlot) = BitVec.ofNat bits q := by
    dsimp only [after, t, bits]
    rw [hheap]
    exact update3_values before.heap
      (before.register .address + BitVec.ofNat _ pointerSlot)
      (before.register .address + BitVec.ofNat _ cursorSlot)
      (before.register .address + BitVec.ofNat _ counterSlot)
      (BitVec.ofNat _ (tableWords full.length q (treeSize q full)))
      (BitVec.ofNat _ (2 + full.length * q)) (BitVec.ofNat _ q)
      hne16_17 hne16_18 hne17_18
  have hCFit := PA06A19PrepareRuntimeLayout026.actual_capacity_fits q full hq
  rw [PA06A19PrepareRuntimeLayout026.capacityExpr_eq _ _ _ hq] at hCFit
  change C < 2 ^ bits at hCFit
  have hTableLt := pointer_lt_capacity full.length q t 0 hq hq
  change tableWords full.length q t + 0 < C at hTableLt
  have hTableFit : Fits bits (tableWords full.length q t) := (by omega : tableWords full.length q t ≤ C).trans_lt hCFit
  have hRomEnd := raw_end_le_capacity full.length q t hq
  change 2 + full.length * q + q ≤ C at hRomEnd
  have hCursorFit : Fits bits (2 + full.length * q) := (by omega : 2 + full.length * q ≤ C).trans_lt hCFit
  have hQfit : Fits bits q := (by omega : q ≤ C).trans_lt hCFit
  refine ⟨(setup_word_control q full used hq left right before hpc ha hd hcode hpcCode).2.2,
    hheader, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a haC
    change scalar q full after.heap a ≤ q
    rw [hcap a haC]
    exact hbound a haC
  · change (after.heap (before.register .address + BitVec.ofNat bits pointerSlot)).toNat = tableWords full.length q t
    rw [hValues.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hTableFit]
  · change (after.heap (before.register .address + BitVec.ofNat bits cursorSlot)).toNat = 2 + full.length * q
    rw [hValues.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hCursorFit]
  · change (after.heap (before.register .address + BitVec.ofNat bits counterSlot)).toNat = q
    rw [hValues.2.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hQfit]
  · intro tool ht
    omega
  · intro a haT
    change a < tableWords full.length q t at haT
    exact hcap a (by omega)
  · intro point _hp hn16 hn17 hn18
    rw [hheap, Function.update_of_ne hn18, Function.update_of_ne hn17, Function.update_of_ne hn16]

theorem loop_result_valid (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original : WordState (indexWidth 32 full.length q)) (hd : BankData q full original)
    (left right : List PackingOp)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ relativeLoopBlock counterSlot left.length body ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ relativeLoopBlock counterSlot left.length body ++ right).length))
    (count : Nat) (state : WordState (indexWidth 32 full.length q)) (hv : valid q full used original state)
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hc : (state.heap (state.register .address + BitVec.ofNat _ counterSlot)).toNat = count) :
    valid q full used original
      (PSTRBuildLower.WordLoop.loopResult (controllerInput q full used) left body right counterSlot (fun _ => 88) count state) := by
  have hb := concrete_body_exits q full used hq original hd left right hcode hpcCode
  induction count generalizing state with
  | zero =>
    obtain ⟨j, hj, h⟩ := hv
    exact ⟨j, hj, current_head q full used original j state h (controllerInput q full used) _⟩
  | succ count ih =>
    have hn : (state.heap (state.register .address + BitVec.ofNat _ counterSlot)).toNat ≠ 0 := by omega
    have ht := PSTRBuildLower.WordLoop.cycle_control (valid q full used original) (controllerInput q full used)
      left body right counterSlot (fun _ => 88) hb state hv hpc ha hn
    exact ih _ ht.2.2.2.2 ht.1 ht.2.1 (by rw [ht.2.2.2.1, hc]; omega)

/-- Full real setup+q-loop result. All source pointer/count qualifications
have been eliminated by the actual33-op setup. The remaining hypotheses
are internal inputs from026/DP and the containing-code physical fits. -/
theorem actual_initialUsed (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false) (hd : BankData q full before)
    (hh : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hbound : CapacityPrefixBounded q (capacityWords 8192 full.length q (treeSize q full))
      (unpackHeap q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) (dataHeap before.heap)))
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ programAt left.length ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ programAt left.length ++ right).length)) :
    let after := packingRun (controllerInput q full used) (left ++ programAt left.length ++ right) (clock q) before
    Current q full used before q after ∧ after.halted = false ∧ after.pc.toNat = 5 * (left.length + 135) ∧
      after.register .address = before.register .address := by
  let rom := controllerInput q full used
  let bits := indexWidth 32 full.length q
  let allCode := left ++ programAt left.length ++ right
  let lead := left ++ setup
  let prepared := packingRun rom allCode 33 before
  let result := PSTRBuildLower.WordLoop.loopResult rom lead body right counterSlot (fun _ => 88) q prepared
  have hlead : lead.length = left.length + 33 := by simp only [lead, List.length_append, setup_length]
  have hcodeLoop : allCode = lead ++ relativeLoopBlock counterSlot lead.length body ++ right := by
    simp only [allCode, programAt, lead, hlead, List.append_assoc]
  have hcodeSetup : allCode = left ++ setup ++ (relativeLoopBlock counterSlot (left.length + 33) body ++ right) := by
    simp only [allCode, programAt, List.append_assoc]
  have hs := setup_current q full used hq left (relativeLoopBlock counterSlot (left.length + 33) body ++ right)
    before hpc ha hd hh hbound (by rw [← hcodeSetup]; exact hcode) (by rw [← hcodeSetup]; exact hpcCode)
  have hcurrent : Current q full used before 0 prepared := by simpa only [← hcodeSetup] using hs
  have hsControl := setup_word_control q full used hq left
    (relativeLoopBlock counterSlot (left.length + 33) body ++ right) before hpc ha hd
    (by rw [← hcodeSetup]; exact hcode) (by rw [← hcodeSetup]; exact hpcCode)
  have hp : prepared.pc.toNat = 5 * lead.length := by
    rw [hlead]
    simpa only [← hcodeSetup] using hsControl.2.1
  have hpFit : Fits bits (5 * lead.length) := (by
    simp only [hlead, allCode, List.length_append, programAt_length]
    omega : 5 * lead.length ≤ 5 * allCode.length).trans_lt hpcCode
  have hpWord : prepared.pc = BitVec.ofNat bits (5 * lead.length) := by
    apply BitVec.eq_of_toNat_eq
    rw [hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpFit]
  have haPrepared : prepared.halted = false := by simpa only [← hcodeSetup] using hsControl.1
  have hcPrepared : (prepared.heap (prepared.register .address + BitVec.ofNat bits counterSlot)).toNat = q :=
    current_remaining q full used before 0 prepared hcurrent
  have hvPrepared : valid q full used before prepared := ⟨0, Nat.zero_le q, hcurrent⟩
  have hb := concrete_body_exits q full used hq before hd lead right
    (by rw [← hcodeLoop]; exact hcode) (by rw [← hcodeLoop]; exact hpcCode)
  have hl := PSTRBuildLower.WordLoop.loop_run (valid q full used before) rom lead body right counterSlot (fun _ => 88)
    hb (by rw [← hcodeLoop]; exact hcode) (by rw [← hcodeLoop]; exact hpcCode)
    q prepared hvPrepared hpWord haPrepared hcPrepared
  have hsteps := loopSteps_eq rom lead right q prepared
  have hloopRun : packingRun rom allCode (102 * q + 5) prepared = result := by
    rw [hcodeLoop]
    rw [hsteps] at hl
    exact hl
  have hrun : packingRun rom allCode (clock q) before = result := by
    rw [show clock q = 33 + (102 * q + 5) by unfold clock; omega, PSTRWordSegments.run_add]
    exact hloopRun
  have hvResult : valid q full used before result := loop_result_valid q full used hq before hd lead right
    (by rw [← hcodeLoop]; exact hcode) (by rw [← hcodeLoop]; exact hpcCode)
    q prepared hvPrepared hpWord haPrepared hcPrepared
  have hControl := PSTRBuildLower.WordLoop.loop_control (valid q full used before) rom lead body right counterSlot (fun _ => 88)
    hb q prepared hvPrepared hpWord haPrepared hcPrepared
  obtain ⟨j, hj, hcur⟩ := hvResult
  have hjq : j = q := by
    have hc : (result.heap (before.register .address +
        BitVec.ofNat (indexWidth 32 full.length q) counterSlot)).toNat = q - j := hcur.remaining
    have heqZero : (result.heap (before.register .address +
        BitVec.ofNat (indexWidth 32 full.length q) counterSlot)).toNat = 0 := by
      have hz := hControl.2.2.2
      change (result.heap (result.register .address +
        BitVec.ofNat (indexWidth 32 full.length q) counterSlot)).toNat = 0 at hz
      rw [hcur.base] at hz
      exact hz
    have remainingZero : q - j = 0 := hc.symm.trans heqZero
    exact Nat.le_antisymm hj (Nat.sub_eq_zero_iff_le.mp remainingZero)
  subst j
  dsimp only
  let after := packingRun rom allCode (clock q) before
  change Current q full used before q after ∧ after.halted = false ∧
    after.pc.toNat = 5 * (left.length + 135) ∧ after.register .address = before.register .address
  simp only [after, hrun]
  refine ⟨hcur, hControl.2.1, ?_, hcur.base⟩
  · change (PSTRBuildLower.WordLoop.loopResult rom lead body right counterSlot (fun _ => 88) q prepared).pc.toNat = _
    rw [hControl.1, BitVec.toNat_ofNat]
    have hendFit : Fits bits (5 * (lead.length + body.length + 14)) := (by
      rw [hcodeLoop]
      simp only [List.length_append, relativeLoopBlock_length]
      omega : 5 * (lead.length + body.length + 14) ≤ 5 * allCode.length).trans_lt hpcCode
    rw [Nat.mod_eq_of_lt hendFit, hlead, body_length]

theorem actual_initialUsed_trace (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q)) :
    (packingDynamicTrace (controllerInput q full used) (left ++ programAt left.length ++ right) (clock q) before).length ≤ 1224 * q + 456 := by
  exact (packingDynamicTrace_length_le _ _ _ before).trans_eq (by unfold clock; omega)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037
