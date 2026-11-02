module

public import Structure.PA06_A19Prepare_RuntimeLayout026_BankWord
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate: the actual fixed layout65 -> transfer22 -> bank47
sequence. Low fields are produced and retained by the preceding real code;
none is accepted as a new raw-input field. Final zeroing is separate. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PA17UniformGenerator035j PA17UniformGenerator035m
  PA17UniformGenerator035p

theorem lowFields_values (N q t width bits : Nat) (heap : Nat → Nat) :
    lowFields N q t width bits heap 9 = N ∧ lowFields N q t width bits heap 10 = q ∧
    lowFields N q t width bits heap 11 = t ∧ lowFields N q t width bits heap 12 = capacityExpr N q t ∧
    lowFields N q t width bits heap 13 = packedExpr (capacityExpr N q t) width bits ∧
    lowFields N q t width bits heap 14 = dimensionsExpr N q t ∧
    lowFields N q t width bits heap 15 = controlExpr (packedExpr (capacityExpr N q t) width bits) (dimensionsExpr N q t) := by
  simp [lowFields]

def sequence (start : Nat) : List PackingOp := layout ++ transfer (start + 65) ++ bankSetup

theorem sequence_length (start : Nat) : (sequence start).length = 134 := rfl

def sequenceClock (N q : Nat) : Nat := 65 + transferClock N q + 47

theorem sequenceClock_eq (N q : Nat) :
    sequenceClock N q = 9 * PA06A19PrepareControlBank017.cacheLength N q + 127 := by
  unfold sequenceClock transferClock
  omega

/-- Actual Nat whole-sequence output. The only incoming heap facts are
the preceding raw phase's M/t and the real temporary header's width/bits. -/
theorem sequence_run (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hM : state.heap 16 = full.length + q + 1)
    (ht : state.heap (20 + 4 * (full.length + q + 1)) = treeSize q full)
    (hw : state.heap 0 = CapacityBits.width q) (hb : state.heap 3 = indexWidth 32 full.length q) :
    let t := treeSize q full
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
    let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
    let originalLayout := lowFields full.length q t (CapacityBits.width q) (indexWidth 32 full.length q) state.heap
    let moved := PA06A19PrepareControlBank017.relocatedHeap originalLayout 0
      (PA06A19PrepareControlBank017.cacheBase full.length q t P) (PA06A19PrepareControlBank017.cacheLength full.length q)
    let fresh := natRun (controllerInput q full used) (left ++ sequence left.length ++ right)
      (sequenceClock full.length q) state
    fresh.halted = false ∧ fresh.pc = 5 * (left.length + 134) ∧ fresh.register .address = CB ∧
      fresh.heap = bankFields full.length q t P CB moved := by
  let rom := controllerInput q full used
  let t := treeSize q full
  let bits := indexWidth 32 full.length q
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  let allCode := left ++ sequence left.length ++ right
  let lead := left ++ layout
  let lastLead := lead ++ transfer lead.length
  let prepared := runOps rom layout state
  let moved := natRun rom allCode (transferClock full.length q) prepared
  have hlead : lead.length = left.length + 65 := by simp only [lead, List.length_append, layout_length]
  have hlast : lastLead.length = left.length + 87 := by
    simp only [lastLead, List.length_append, transfer_length, hlead]
  have hcode : allCode = lead ++ transfer lead.length ++ (bankSetup ++ right) := by
    simp only [allCode, sequence, lead, hlead, List.append_assoc]
  have hcodeLast : allCode = lastLead ++ bankSetup ++ right := by
    rw [hcode]
    simp only [lastLead, List.append_assoc]
  have hdata := layout_data q full used state (full.length + q + 1) t
    (CapacityBits.width q) bits hM ht hw hb
  have hP : packedExpr (capacityExpr full.length q t) (CapacityBits.width q) bits = P :=
    packedExpr_eq full.length q t hq
  have hCtrl : controlExpr P (dimensionsExpr full.length q t) = CB := controlExpr_eq full.length q t P
  have hpCB : prepared.register .address = CB := by rw [hdata.2, hP, hCtrl]
  have hpH : prepared.heap = lowFields full.length q t (CapacityBits.width q) bits state.heap := hdata.1
  have hpPC : prepared.pc = 5 * lead.length := by
    rw [runOps_pc rom layout state layout_noJump, hpc, layout_length, hlead]
    omega
  have hpA : prepared.halted = false := (runOps_halted rom layout state).trans ha
  have hpM : prepared.heap 16 = PA06A19PrepareControlBank017.mass full.length q :=
    (layout_frame q full used state (full.length + q + 1) t (CapacityBits.width q) bits
      hM ht hw hb 16 (Or.inr (by decide))).trans hM
  have hp15 : prepared.heap 15 = CB := by
    rw [hpH, (lowFields_values full.length q t (CapacityBits.width q) bits state.heap).2.2.2.2.2.2, hP, hCtrl]
  have hmove := transfer_run full.length q t P hq rom lead (bankSetup ++ right) prepared hpPC hpA hpCB hpM hp15
  have hmove' : moved.register .address = CB ∧ moved.pc = 5 * (lead.length + 22) ∧
      moved.halted = false ∧ moved.heap = PA06A19PrepareControlBank017.relocatedHeap prepared.heap 0
        (PA06A19PrepareControlBank017.cacheBase full.length q t P) (PA06A19PrepareControlBank017.cacheLength full.length q) := by
    simpa only [moved, hcode] using hmove
  have hmLow (low : Nat) (hlow : low ≤ 15) : moved.heap low = prepared.heap low := by
    rw [hmove'.2.2.2]
    exact PA06A19PrepareControlBank017.relocatedHeap_frame _ _ _ _ low
      (Or.inl (by unfold PA06A19PrepareControlBank017.cacheBase; omega))
  have hm9 : moved.heap 9 = full.length := by
    rw [hmLow 9 (by decide), hpH]
    exact (lowFields_values full.length q t (CapacityBits.width q) bits state.heap).1
  have hm10 : moved.heap 10 = q := by
    rw [hmLow 10 (by decide), hpH]
    exact (lowFields_values full.length q t (CapacityBits.width q) bits state.heap).2.1
  have hm11 : moved.heap 11 = t := by
    rw [hmLow 11 (by decide), hpH]
    exact (lowFields_values full.length q t (CapacityBits.width q) bits state.heap).2.2.1
  have hm12 : moved.heap 12 = capacityExpr full.length q t := by
    rw [hmLow 12 (by decide), hpH]
    exact (lowFields_values full.length q t (CapacityBits.width q) bits state.heap).2.2.2.1
  have hm13 : moved.heap 13 = P := by
    rw [hmLow 13 (by decide), hpH]
    exact (lowFields_values full.length q t (CapacityBits.width q) bits state.heap).2.2.2.2.1.trans hP
  have hmCB16 : 16 ≤ moved.register .address := by
    rw [hmove'.1]
    dsimp only [CB, PA06A19PrepareControlBank017.controlBase, PA06A19PrepareControlBank017.dimensions,
      PA06A19PrepareControlBank017.mass]
    omega
  have hbankHeap := bankSetup_heap rom moved full.length q t P hmCB16 hm9 hm10 hm11 hm12 hm13
  have hfirst : natRun rom allCode 65 state = prepared := by
    have hh := layout_run rom left (transfer (left.length + 65) ++ bankSetup ++ right) state hpc ha
    simpa only [allCode, sequence, List.append_assoc] using hh
  have hlastRun : natRun rom allCode 47 moved = runOps rom bankSetup moved := by
    rw [hcodeLast]
    exact bankSetup_run rom lastLead right moved
      (by rw [hlast]; have hh := hmove'.2.1; rw [hlead] at hh; omega) hmove'.2.2.1
  have hrun : natRun rom allCode (sequenceClock full.length q) state = runOps rom bankSetup moved := by
    rw [sequenceClock, natRun_add, natRun_add, hfirst]
    exact hlastRun
  dsimp only
  let fresh := natRun rom allCode (sequenceClock full.length q) state
  change fresh.halted = false ∧ fresh.pc = 5 * (left.length + 134) ∧ fresh.register .address = CB ∧
    fresh.heap = bankFields full.length q t P CB
      (PA06A19PrepareControlBank017.relocatedHeap
        (lowFields full.length q t (CapacityBits.width q) bits state.heap) 0
        (PA06A19PrepareControlBank017.cacheBase full.length q t P) (PA06A19PrepareControlBank017.cacheLength full.length q))
  simp only [fresh, hrun]
  refine ⟨(runOps_halted rom bankSetup moved).trans hmove'.2.2.1, ?_,
    (bankSetup_address rom moved).trans hmove'.1, ?_⟩
  · rw [runOps_pc rom bankSetup moved bankSetup_noJump, bankSetup_length, hmove'.2.1, hlead]
    omega
  · rw [hbankHeap, hmove'.1, hmove'.2.2.2, hpH]

theorem actual_lowFields_bound (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (heap : Nat → Nat)
    (hwords : ∀ position < PA06A19PrepareControlBank017.cacheLength full.length q,
      heap position ≤ 2 ^ indexWidth 32 full.length q - 1)
    (position : Nat) (hp : position < PA06A19PrepareControlBank017.cacheLength full.length q) :
    lowFields full.length q (treeSize q full) (CapacityBits.width q) (indexWidth 32 full.length q) heap position ≤
      2 ^ indexWidth 32 full.length q - 1 := by
  have hold := hwords position hp
  have hinput := PA17GeneratorStatic048.input_le_maxWord full.length q 0 hq (by omega)
  have htree := PA06A19PrepareControlBank017.treeSize_bound full
  have hc := actual_capacity_fits q full hq
  have hp' := actual_packed_fits q full hq
  have hctrl := actual_control_fits q full hq
  change capacityExpr full.length q (treeSize q full) < 2 ^ indexWidth 32 full.length q at hc
  change packedExpr (capacityExpr full.length q (treeSize q full)) (CapacityBits.width q)
    (indexWidth 32 full.length q) < 2 ^ indexWidth 32 full.length q at hp'
  change controlExpr (packedExpr (capacityExpr full.length q (treeSize q full)) (CapacityBits.width q)
    (indexWidth 32 full.length q)) (dimensionsExpr full.length q (treeSize q full)) <
      2 ^ indexWidth 32 full.length q at hctrl
  have hD : dimensionsExpr full.length q (treeSize q full) ≤ 2 ^ indexWidth 32 full.length q - 1 := by
    unfold controlExpr at hctrl
    omega
  unfold lowFields
  simp only [Function.update_apply]
  split_ifs <;> omega

/-- Whole-sequence safety is composed from three proved actual segments.
The only source-value premise is the incoming Word view's finite values. -/
theorem sequence_safe (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hr : RegistersLE (2 ^ indexWidth 32 full.length q - 1) state)
    (hM : state.heap 16 = full.length + q + 1)
    (ht : state.heap (20 + 4 * (full.length + q + 1)) = treeSize q full)
    (hw : state.heap 0 = CapacityBits.width q) (hb : state.heap 3 = indexWidth 32 full.length q)
    (hwords : ∀ position < PA06A19PrepareControlBank017.cacheLength full.length q,
      state.heap position ≤ 2 ^ indexWidth 32 full.length q - 1)
    (hpcB : 5 * (left ++ sequence left.length ++ right).length ≤ 2 ^ indexWidth 32 full.length q - 1) :
    RunSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) (left ++ sequence left.length ++ right) (sequenceClock full.length q) state := by
  let rom := controllerInput q full used
  let t := treeSize q full
  let bits := indexWidth 32 full.length q
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  let B := 2 ^ bits - 1
  let H := PA06A19PrepareRuntimeHeader019.heapWords full.length q t
  let allCode := left ++ sequence left.length ++ right
  let lead := left ++ layout
  let lastLead := lead ++ transfer lead.length
  let prepared := runOps rom layout state
  let moved := natRun rom allCode (transferClock full.length q) prepared
  have hlead : lead.length = left.length + 65 := by simp only [lead, List.length_append, layout_length]
  have hlast : lastLead.length = left.length + 87 := by
    simp only [lastLead, List.length_append, transfer_length, hlead]
  have hcode : allCode = lead ++ transfer lead.length ++ (bankSetup ++ right) := by
    simp only [allCode, sequence, lead, hlead, List.append_assoc]
  have hcodeLast : allCode = lastLead ++ bankSetup ++ right := by
    rw [hcode]
    simp only [lastLead, List.append_assoc]
  have hdata := layout_data q full used state (full.length + q + 1) t
    (CapacityBits.width q) bits hM ht hw hb
  have hP : packedExpr (capacityExpr full.length q t) (CapacityBits.width q) bits = P :=
    packedExpr_eq full.length q t hq
  have hCtrl : controlExpr P (dimensionsExpr full.length q t) = CB := controlExpr_eq full.length q t P
  have hpCB : prepared.register .address = CB := by rw [hdata.2, hP, hCtrl]
  have hpH : prepared.heap = lowFields full.length q t (CapacityBits.width q) bits state.heap := hdata.1
  have hpPC : prepared.pc = 5 * lead.length := by
    rw [runOps_pc rom layout state layout_noJump, hpc, layout_length, hlead]
    omega
  have hpA : prepared.halted = false := (runOps_halted rom layout state).trans ha
  have hpM : prepared.heap 16 = PA06A19PrepareControlBank017.mass full.length q :=
    (layout_frame q full used state (full.length + q + 1) t (CapacityBits.width q) bits
      hM ht hw hb 16 (Or.inr (by decide))).trans hM
  have hp15 : prepared.heap 15 = CB := by
    rw [hpH, (lowFields_values full.length q t (CapacityBits.width q) bits state.heap).2.2.2.2.2.2, hP, hCtrl]
  have hpWords (position : Nat) (hposition : position < PA06A19PrepareControlBank017.cacheLength full.length q) :
      prepared.heap position ≤ B := by
    rw [hpH]
    exact actual_lowFields_bound q full hq state.heap hwords position hposition
  have hpRegs : RegistersLE B prepared :=
    (actual_layout_numeric q full used hq state hr hM ht hw hb).final _ _ _ _ _
  have hLayoutSafe : RunSafe B H rom allCode 65 state := by
    have hh := layout_safe q full used hq left (transfer (left.length + 65) ++ bankSetup ++ right)
      state hpc ha hr hM ht hw hb
    simpa only [allCode, sequence, List.append_assoc] using hh
  have hfirst : natRun rom allCode 65 state = prepared := by
    have hh := layout_run rom left (transfer (left.length + 65) ++ bankSetup ++ right) state hpc ha
    simpa only [allCode, sequence, List.append_assoc] using hh
  have hMoveSafe := actual_transfer_safe q full used hq lead (bankSetup ++ right) prepared hpPC hpA hpRegs
    hpCB hpM hp15 hpWords (by rw [← hcode]; exact hpcB)
  have hMoveSafe' : RunSafe B H rom allCode (transferClock full.length q) prepared := by
    simpa only [hcode] using hMoveSafe
  have hmove := transfer_run full.length q t P hq rom lead (bankSetup ++ right) prepared hpPC hpA hpCB hpM hp15
  have hmove' : moved.register .address = CB ∧ moved.pc = 5 * (lead.length + 22) ∧
      moved.halted = false ∧ moved.heap = PA06A19PrepareControlBank017.relocatedHeap prepared.heap 0
        (PA06A19PrepareControlBank017.cacheBase full.length q t P) (PA06A19PrepareControlBank017.cacheLength full.length q) := by
    simpa only [moved, hcode] using hmove
  have hmLow (low : Nat) (hlow : low ≤ 15) : moved.heap low = prepared.heap low := by
    rw [hmove'.2.2.2]
    exact PA06A19PrepareControlBank017.relocatedHeap_frame _ _ _ _ low
      (Or.inl (by unfold PA06A19PrepareControlBank017.cacheBase; omega))
  have hm9 : moved.heap 9 = full.length := by
    rw [hmLow 9 (by decide), hpH]
    exact (lowFields_values full.length q t (CapacityBits.width q) bits state.heap).1
  have hm10 : moved.heap 10 = q := by
    rw [hmLow 10 (by decide), hpH]
    exact (lowFields_values full.length q t (CapacityBits.width q) bits state.heap).2.1
  have hm11 : moved.heap 11 = t := by
    rw [hmLow 11 (by decide), hpH]
    exact (lowFields_values full.length q t (CapacityBits.width q) bits state.heap).2.2.1
  have hm12 : moved.heap 12 = capacityExpr full.length q t := by
    rw [hmLow 12 (by decide), hpH]
    exact (lowFields_values full.length q t (CapacityBits.width q) bits state.heap).2.2.2.1
  have hm13 : moved.heap 13 = P := by
    rw [hmLow 13 (by decide), hpH]
    exact (lowFields_values full.length q t (CapacityBits.width q) bits state.heap).2.2.2.2.1.trans hP
  have hbankSafe := bankSetup_safe q full used hq lastLead right moved
    (by rw [hlast]; have hh := hmove'.2.1; rw [hlead] at hh; omega) hmove'.2.2.1
    (hMoveSafe'.final _ _ _ _ _).1 hmove'.1 hm9 hm10 hm11 hm12 hm13
  have hbankSafe' : RunSafe B H rom allCode 47 moved := by
    simpa only [hcodeLast] using hbankSafe
  have hfirstSafe := RunSafe.add B H rom allCode 65 (transferClock full.length q) state
    hLayoutSafe (by rw [hfirst]; exact hMoveSafe')
  have hfirstRun : natRun rom allCode (65 + transferClock full.length q) state = moved := by
    rw [natRun_add, hfirst]
  exact RunSafe.add B H rom allCode (65 + transferClock full.length q) 47 state hfirstSafe
    (by rw [hfirstRun]; exact hbankSafe')

theorem sequence0_code_le : ∀ value ∈ packingCode (sequence 0), value ≤ 8192 := by decide

theorem sequence0_code_fit (N q : Nat) (hq : 0 < q) :
    WordsFit (indexWidth 32 N q) (packingCode (sequence 0)) := by
  intro value hv
  exact ((sequence0_code_le value hv).trans (maxWord_8192 N q hq)).trans_lt
    (PA17GeneratorStatic048.maxWord_fits _)

theorem sequence0_pc_le (N q : Nat) (hq : 0 < q) :
    5 * (sequence 0).length ≤ 2 ^ indexWidth 32 N q - 1 :=
  (by decide : 5 * (sequence 0).length ≤ 8192).trans (maxWord_8192 N q hq)

theorem sequence0_pc_fit (N q : Nat) (hq : 0 < q) :
    Fits (indexWidth 32 N q) (5 * (sequence 0).length) :=
  (sequence0_pc_le N q hq).trans_lt (PA17GeneratorStatic048.maxWord_fits _)

/-- Actual whole fixed sequence: all low-field and bank-value premises
of the components are discharged by earlier real instructions. -/
theorem actual_sequence_word (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) :
    packingRun (controllerInput q full used) (sequence 0) (sequenceClock full.length q) state =
      (natRun (controllerInput q full used) (sequence 0) (sequenceClock full.length q)
        (PA06A19PrepareRuntimeHeader019.natView state)).toWord (indexWidth 32 full.length q) := by
  let start := PA06A19PrepareRuntimeHeader019.natView state
  have hstartPC : start.pc = 5 * ([] : List PackingOp).length := by
    change state.pc.toNat = 0
    rw [hpc]
    rfl
  have hv := header_layout_values q full hq state hh
  have hwords (position : Nat) (_hp : position < PA06A19PrepareControlBank017.cacheLength full.length q) :
      start.heap position ≤ 2 ^ indexWidth 32 full.length q - 1 := by
    have hs := (state.heap (BitVec.ofNat _ position)).toNat_lt_twoPow_of_le
      (Nat.le_refl (indexWidth 32 full.length q))
    change (state.heap (BitVec.ofNat _ position)).toNat ≤ _
    omega
  have hs := sequence_safe q full used hq [] [] start hstartPC ha
    (PA06A19PrepareRuntimeHeader019.natView_registers state) hM ht hv.1 hv.2 hwords
    (by simpa only [List.nil_append, List.append_nil, List.length_nil] using sequence0_pc_le full.length q hq)
  have hs' : RunSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) (sequence 0) (sequenceClock full.length q) start := by
    simpa only [List.nil_append, List.append_nil, List.length_nil] using hs
  have hw := actual_word_run _ _ _ _ _ (sequenceClock full.length q) start hs'
    (PA17GeneratorStatic048.maxWord_fits _) (sequence0_code_fit full.length q hq)
    (sequence0_pc_fit full.length q hq) (sequenceClock full.length q) le_rfl
  simpa only [start, PA06A19PrepareRuntimeHeader019.natView_toWord] using hw

theorem actual_sequence_data (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) :
    let t := treeSize q full
    let bits := indexWidth 32 full.length q
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
    let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
    let originalLayout := lowFields full.length q t (CapacityBits.width q) bits
      (PA06A19PrepareRuntimeHeader019.natView state).heap
    let moved := PA06A19PrepareControlBank017.relocatedHeap originalLayout 0
      (PA06A19PrepareControlBank017.cacheBase full.length q t P) (PA06A19PrepareControlBank017.cacheLength full.length q)
    let fresh := packingRun (controllerInput q full used) (sequence 0) (sequenceClock full.length q) state
    fresh.halted = false ∧ fresh.pc.toNat = 670 ∧ (fresh.register .address).toNat = CB ∧
    ∀ address, fresh.heap address = BitVec.ofNat bits (bankFields full.length q t P CB moved address.toNat) := by
  let start := PA06A19PrepareRuntimeHeader019.natView state
  let t := treeSize q full
  let bits := indexWidth 32 full.length q
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  let expectedHeap := bankFields full.length q t P CB
    (PA06A19PrepareControlBank017.relocatedHeap
      (lowFields full.length q t (CapacityBits.width q) bits start.heap) 0
      (PA06A19PrepareControlBank017.cacheBase full.length q t P) (PA06A19PrepareControlBank017.cacheLength full.length q))
  have hv := header_layout_values q full hq state hh
  have hn := sequence_run q full used hq [] [] start
    (by change state.pc.toNat = 0; rw [hpc]; rfl) ha hM ht hv.1 hv.2
  have hn' :
      (natRun (controllerInput q full used) (sequence 0) (sequenceClock full.length q) start).halted = false ∧
      (natRun (controllerInput q full used) (sequence 0) (sequenceClock full.length q) start).pc = 670 ∧
      (natRun (controllerInput q full used) (sequence 0) (sequenceClock full.length q) start).register .address = CB ∧
      (natRun (controllerInput q full used) (sequence 0) (sequenceClock full.length q) start).heap = expectedHeap := by
    simpa only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] using hn
  have hCBfit : Fits bits CB := by
    dsimp only [CB, P, t, bits]
    simpa only [Nat.add_zero] using actual_bank_field_fits q full hq 0 (by decide)
  dsimp only
  simp only [actual_sequence_word q full used hq state hpc ha hM ht hh]
  refine ⟨hn'.1, ?_, ?_, ?_⟩
  · change (BitVec.ofNat bits (natRun _ _ _ start).pc).toNat = 670
    rw [hn'.2.1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simpa only [sequence_length, AlgorithmClaims.Fits, bits] using sequence0_pc_fit full.length q hq)]
  · change (BitVec.ofNat bits ((natRun _ _ _ start).register .address)).toNat = _
    rw [hn'.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hCBfit]
  · intro address
    change BitVec.ofNat bits ((natRun _ _ _ start).heap address.toNat) = _
    rw [hn'.2.2.2]

/-- This includes the actual Header and every original raw-cache word
below CB outside the intentionally used low scratch slots9..15. -/
theorem actual_sequence_frame (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (address : BitVec (indexWidth 32 full.length q)) (hlow : address.toNat < 9 ∨ 16 ≤ address.toNat)
    (haddr : address.toNat < PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
      (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))) :
    (packingRun (controllerInput q full used) (sequence 0) (sequenceClock full.length q) state).heap address = state.heap address := by
  have hne (offset : Nat) : address.toNat ≠
      PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
        (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) + offset := by
    omega
  have hd := (actual_sequence_data q full used hq state hpc ha hM ht hh).2.2.2 address
  rw [hd]
  unfold bankFields
  rw [Function.update_of_ne (hne 6), Function.update_of_ne (hne 5),
    Function.update_of_ne (hne 4), Function.update_of_ne (hne 3),
    Function.update_of_ne (hne 2), Function.update_of_ne (hne 1), Function.update_of_ne (hne 0)]
  rw [PA06A19PrepareControlBank017.relocatedHeap_frame _ _ _ _ address.toNat (Or.inl (by
    unfold PA06A19PrepareControlBank017.cacheBase
    omega))]
  unfold lowFields
  simp only [Function.update_of_ne (show address.toNat ≠ 9 by omega),
    Function.update_of_ne (show address.toNat ≠ 10 by omega),
    Function.update_of_ne (show address.toNat ≠ 11 by omega),
    Function.update_of_ne (show address.toNat ≠ 12 by omega),
    Function.update_of_ne (show address.toNat ≠ 13 by omega),
    Function.update_of_ne (show address.toNat ≠ 14 by omega),
    Function.update_of_ne (show address.toNat ≠ 15 by omega)]
  simp only [PA06A19PrepareRuntimeHeader019.natView, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026
