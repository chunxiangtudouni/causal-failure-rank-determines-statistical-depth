module

public import Structure.PA06_A19Prepare_RuntimeLayout026_Word
public import Structure.PA06_A19Prepare_ControlBank017_Safety
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate: actual setup9 -> relocated copy11 -> restore2. All PC
transitions are the existing machine's transitions. The copy's source and
target come from real setup instructions, and CB is really reloaded at15. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PA17UniformGenerator035j PA17UniformGenerator035m
  PA17UniformGenerator035p

theorem setupCopy_noJump : ∀ op ∈ setupCopy, NoJump op := by simp [setupCopy, NoJump]
theorem restoreControl_noJump : ∀ op ∈ restoreControl, NoJump op := by simp [restoreControl, NoJump]

theorem setupCopy_numeric (rom : PhysicalROM) (B H CB M : Nat)
    (hsmall : 512 ≤ B) (hH : 17 ≤ H) (htarget : CB + 512 ≤ B) (hcount : 21 + 5 * M ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hM : state.heap 16 = M) : NumericSafe B H rom setupCopy state := by
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 9 at hc
    interval_cases count <;> cases register <;>
      simp +decide [setupCopy, runOps, natExecuteOp, natArithmetic, Op.execute,
        Instruction.execute, hCB, hM]
    all_goals omega
  · intro count hc
    change count < 9 at hc
    interval_cases count <;>
      simp +decide [setupCopy, runOps, natExecuteOp, Op.execute,
        Instruction.execute, NatAccessFits, AccessFits]
    all_goals omega

theorem restoreControl_numeric (rom : PhysicalROM) (B H CB : Nat)
    (hsmall : 15 ≤ B) (hH : 16 ≤ H) (hCB : CB ≤ B)
    (state : NatState) (hr : RegistersLE B state) (h15 : state.heap 15 = CB) :
    NumericSafe B H rom restoreControl state := by
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 2 at hc
    interval_cases count <;> cases register <;>
      simp +decide [restoreControl, runOps, natExecuteOp, Op.execute, Instruction.execute, h15]
    all_goals omega
  · intro count hc
    change count < 2 at hc
    interval_cases count <;>
      simp +decide [restoreControl, runOps, natExecuteOp, Op.execute, Instruction.execute,
        NatAccessFits, AccessFits]
    all_goals omega

def transfer (start : Nat) : List PackingOp :=
  setupCopy ++ PA06A19PrepareControlBank017.programAt (start + 9) ++ restoreControl

theorem transfer_length (start : Nat) : (transfer start).length = 22 := rfl

def transferClock (N q : Nat) : Nat := 9 * PA06A19PrepareControlBank017.cacheLength N q + 15

/-- Real Nat execution; in particular address is not reset or recovered
by a semantic assignment. The final heap is the genuine forward copy. -/
theorem transfer_run (N q t P : Nat) (hq : 0 < q) (rom : PhysicalROM)
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hCB : state.register .address = PA06A19PrepareControlBank017.controlBase N q t P)
    (hM : state.heap 16 = PA06A19PrepareControlBank017.mass N q)
    (h15 : state.heap 15 = PA06A19PrepareControlBank017.controlBase N q t P) :
    let fresh := natRun rom (left ++ transfer left.length ++ right) (transferClock N q) state
    fresh.register .address = PA06A19PrepareControlBank017.controlBase N q t P ∧
    fresh.pc = 5 * (left.length + 22) ∧ fresh.halted = false ∧
    fresh.heap = PA06A19PrepareControlBank017.relocatedHeap state.heap 0
      (PA06A19PrepareControlBank017.cacheBase N q t P) (PA06A19PrepareControlBank017.cacheLength N q) := by
  let allCode := left ++ transfer left.length ++ right
  let lead := left ++ setupCopy
  let lastLead := lead ++ PA06A19PrepareControlBank017.programAt lead.length
  let prepared := runOps rom setupCopy state
  let copied := natRun rom allCode (9 * PA06A19PrepareControlBank017.cacheLength N q + 4) prepared
  have hlead : lead.length = left.length + 9 := by
    simp only [lead, List.length_append, setupCopy_length]
  have hlast : lastLead.length = left.length + 20 := by
    simp only [lastLead, List.length_append, PA06A19PrepareControlBank017.programAt_length, hlead]
  have hcode : allCode = lead ++ PA06A19PrepareControlBank017.programAt lead.length ++ (restoreControl ++ right) := by
    simp only [allCode, transfer, lead, hlead, List.append_assoc]
  have hcodeLast : allCode = lastLead ++ restoreControl ++ right := by
    rw [hcode]
    simp only [lastLead, List.append_assoc]
  have hsetup := setupCopy_data rom state
  have hpreparedPC : prepared.pc = 5 * lead.length := by
    rw [runOps_pc rom setupCopy state setupCopy_noJump, hpc, setupCopy_length, hlead]
    omega
  have hpreparedA : prepared.halted = false := (runOps_halted rom setupCopy state).trans ha
  have hpreparedH : prepared.heap = state.heap := hsetup.2.2.2
  have hsource : prepared.register .address = 0 := hsetup.1
  have htarget : prepared.register .index = PA06A19PrepareControlBank017.cacheBase N q t P := by
    rw [hsetup.2.1, hCB]
    rfl
  have hcount : prepared.register .total = PA06A19PrepareControlBank017.cacheLength N q := by
    rw [hsetup.2.2.1, hM]
    rfl
  have hd : 0 + PA06A19PrepareControlBank017.cacheLength N q ≤
      PA06A19PrepareControlBank017.cacheBase N q t P := by
    simpa only [Nat.zero_add] using PA06A19PrepareControlBank017.source_target_disjoint N q t P hq
  have hcopy := PA06A19PrepareControlBank017.copy_run rom lead (restoreControl ++ right)
    0 (PA06A19PrepareControlBank017.cacheBase N q t P) (PA06A19PrepareControlBank017.cacheLength N q)
    prepared hpreparedPC hpreparedA hsource htarget hcount hd
  have hcopied : PA06A19PrepareControlBank017.CopyInv 0
      (PA06A19PrepareControlBank017.cacheBase N q t P) prepared.heap
      (PA06A19PrepareControlBank017.cacheLength N q) 0 copied ∧
      copied.pc = 5 * (lead.length + 11) ∧ copied.halted = false := by
    simpa only [copied, hcode] using hcopy
  have hcopyHeap : copied.heap = PA06A19PrepareControlBank017.relocatedHeap state.heap 0
      (PA06A19PrepareControlBank017.cacheBase N q t P) (PA06A19PrepareControlBank017.cacheLength N q) := by
    rw [hcopied.1.2.2.2.2.2, hpreparedH]
  have hcopied15 : copied.heap 15 = PA06A19PrepareControlBank017.controlBase N q t P := by
    rw [hcopyHeap, PA06A19PrepareControlBank017.relocatedHeap_frame _ _ _ _ 15
      (Or.inl (by unfold PA06A19PrepareControlBank017.cacheBase; omega))]
    exact h15
  have hsetupRun : natRun rom allCode 9 state = prepared := by
    have hh := natRun_of_straight_segment rom
      (left ++ setupCopy ++ (PA06A19PrepareControlBank017.programAt (left.length + 9) ++ restoreControl ++ right))
      setupCopy left.length (by simp only [List.length_append]; omega)
      (PA17UniformGenerator035a.segment_index left setupCopy _) setupCopy_noJump state hpc ha
    simpa only [allCode, transfer, List.append_assoc, setupCopy_length] using hh
  have hrestoreRun : natRun rom allCode 2 copied = runOps rom restoreControl copied := by
    rw [hcodeLast]
    exact natRun_of_straight_segment rom (lastLead ++ restoreControl ++ right) restoreControl lastLead.length
      (by simp only [List.length_append]; omega) (PA17UniformGenerator035a.segment_index lastLead restoreControl right)
      restoreControl_noJump copied (by rw [hlast]; have hp := hcopied.2.1; rw [hlead] at hp; omega) hcopied.2.2
  have hrun : natRun rom allCode (transferClock N q) state = runOps rom restoreControl copied := by
    rw [show transferClock N q = 9 + (9 * PA06A19PrepareControlBank017.cacheLength N q + 4) + 2 by
      unfold transferClock; omega, natRun_add, natRun_add, hsetupRun]
    exact hrestoreRun
  dsimp only
  let fresh := natRun rom allCode (transferClock N q) state
  change fresh.register .address = PA06A19PrepareControlBank017.controlBase N q t P ∧
    fresh.pc = 5 * (left.length + 22) ∧ fresh.halted = false ∧
    fresh.heap = PA06A19PrepareControlBank017.relocatedHeap state.heap 0
      (PA06A19PrepareControlBank017.cacheBase N q t P) (PA06A19PrepareControlBank017.cacheLength N q)
  simp only [fresh, hrun]
  refine ⟨(restoreControl_data rom copied).1.trans hcopied15, ?_,
    (runOps_halted rom restoreControl copied).trans hcopied.2.2,
    (restoreControl_data rom copied).2.trans hcopyHeap⟩
  rw [runOps_pc rom restoreControl copied restoreControl_noJump, restoreControl_length, hcopied.2.1, hlead]
  omega

/-- Internal finite source/target room is consumed by the existing copy
safety proof; no all-prefix safety conclusion is accepted as a premise. -/
theorem transfer_safe (N q t P : Nat) (hq : 0 < q) (rom : PhysicalROM) (B H : Nat)
    (hsmall : 512 ≤ B) (hH : 17 ≤ H)
    (hsourceB : PA06A19PrepareControlBank017.cacheLength N q ≤ B)
    (hsourceH : PA06A19PrepareControlBank017.cacheLength N q ≤ H)
    (htargetB : PA06A19PrepareControlBank017.cacheBase N q t P +
      PA06A19PrepareControlBank017.cacheLength N q ≤ B)
    (htargetH : PA06A19PrepareControlBank017.cacheBase N q t P +
      PA06A19PrepareControlBank017.cacheLength N q ≤ H)
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (hCB : state.register .address = PA06A19PrepareControlBank017.controlBase N q t P)
    (hM : state.heap 16 = PA06A19PrepareControlBank017.mass N q)
    (h15 : state.heap 15 = PA06A19PrepareControlBank017.controlBase N q t P)
    (hwords : ∀ position < PA06A19PrepareControlBank017.cacheLength N q, state.heap position ≤ B)
    (hpcB : 5 * (left ++ transfer left.length ++ right).length ≤ B) :
    RunSafe B H rom (left ++ transfer left.length ++ right) (transferClock N q) state := by
  let allCode := left ++ transfer left.length ++ right
  let lead := left ++ setupCopy
  let lastLead := lead ++ PA06A19PrepareControlBank017.programAt lead.length
  let prepared := runOps rom setupCopy state
  let copied := natRun rom allCode (9 * PA06A19PrepareControlBank017.cacheLength N q + 4) prepared
  have hlead : lead.length = left.length + 9 := by
    simp only [lead, List.length_append, setupCopy_length]
  have hlast : lastLead.length = left.length + 20 := by
    simp only [lastLead, List.length_append, PA06A19PrepareControlBank017.programAt_length, hlead]
  have hcode : allCode = lead ++ PA06A19PrepareControlBank017.programAt lead.length ++ (restoreControl ++ right) := by
    simp only [allCode, transfer, lead, hlead, List.append_assoc]
  have hcodeLast : allCode = lastLead ++ restoreControl ++ right := by
    rw [hcode]
    simp only [lastLead, List.append_assoc]
  have hCB_B : PA06A19PrepareControlBank017.controlBase N q t P ≤ B := by
    unfold PA06A19PrepareControlBank017.cacheBase at htargetB
    omega
  have hsetupNum := setupCopy_numeric rom B H (PA06A19PrepareControlBank017.controlBase N q t P)
    (PA06A19PrepareControlBank017.mass N q) hsmall hH
    (by change PA06A19PrepareControlBank017.cacheBase N q t P ≤ B; omega)
    (by simpa only [PA06A19PrepareControlBank017.cacheLength] using hsourceB) state hr hCB hM
  have hsetupSafe : RunSafe B H rom allCode 9 state := by
    have hh := straight_segment_safe rom B H left setupCopy
      (PA06A19PrepareControlBank017.programAt (left.length + 9) ++ restoreControl ++ right)
      setupCopy_noJump state hpc ha hsetupNum
    simpa only [allCode, transfer, List.append_assoc, setupCopy_length] using hh
  have hsetupRun : natRun rom allCode 9 state = prepared := by
    have hh := natRun_of_straight_segment rom
      (left ++ setupCopy ++ (PA06A19PrepareControlBank017.programAt (left.length + 9) ++ restoreControl ++ right))
      setupCopy left.length (by simp only [List.length_append]; omega)
      (PA17UniformGenerator035a.segment_index left setupCopy _) setupCopy_noJump state hpc ha
    simpa only [allCode, transfer, List.append_assoc, setupCopy_length] using hh
  have hsetup := setupCopy_data rom state
  have hpreparedH : prepared.heap = state.heap := hsetup.2.2.2
  have hp : prepared.pc = 5 * lead.length := by
    rw [runOps_pc rom setupCopy state setupCopy_noJump, hpc, setupCopy_length, hlead]
    omega
  have hactive : prepared.halted = false := (runOps_halted rom setupCopy state).trans ha
  have hsource : prepared.register .address = 0 := hsetup.1
  have htarget : prepared.register .index = PA06A19PrepareControlBank017.cacheBase N q t P := by
    rw [hsetup.2.1, hCB]
    rfl
  have hn : prepared.register .total = PA06A19PrepareControlBank017.cacheLength N q := by
    rw [hsetup.2.2.1, hM]
    rfl
  have hcopySafe := PA06A19PrepareControlBank017.copy_safe rom B H lead (restoreControl ++ right)
    0 (PA06A19PrepareControlBank017.cacheBase N q t P) (PA06A19PrepareControlBank017.cacheLength N q)
    prepared hp hactive (hsetupNum.final _ _ _ _ _) (by omega) hsource htarget hn
    (by simpa only [Nat.zero_add] using PA06A19PrepareControlBank017.source_target_disjoint N q t P hq)
    (by simpa only [Nat.zero_add] using hsourceB) (by simpa only [Nat.zero_add] using hsourceH)
    htargetB htargetH (by
      intro position hposition
      rw [hpreparedH, Nat.zero_add]
      exact hwords position hposition)
    (by rw [← hcode]; exact hpcB)
  have hcopySafe' : RunSafe B H rom allCode
      (9 * PA06A19PrepareControlBank017.cacheLength N q + 4) prepared := by
    simpa only [hcode] using hcopySafe
  have hcopy := PA06A19PrepareControlBank017.copy_run rom lead (restoreControl ++ right)
    0 (PA06A19PrepareControlBank017.cacheBase N q t P) (PA06A19PrepareControlBank017.cacheLength N q)
    prepared hp hactive hsource htarget hn
    (by simpa only [Nat.zero_add] using PA06A19PrepareControlBank017.source_target_disjoint N q t P hq)
  have hcopied : PA06A19PrepareControlBank017.CopyInv 0
      (PA06A19PrepareControlBank017.cacheBase N q t P) prepared.heap
      (PA06A19PrepareControlBank017.cacheLength N q) 0 copied ∧
      copied.pc = 5 * (lead.length + 11) ∧ copied.halted = false := by
    simpa only [copied, hcode] using hcopy
  have hcopied15 : copied.heap 15 = PA06A19PrepareControlBank017.controlBase N q t P := by
    rw [hcopied.1.2.2.2.2.2, PA06A19PrepareControlBank017.relocatedHeap_frame _ _ _ _ 15
      (Or.inl (by unfold PA06A19PrepareControlBank017.cacheBase; omega)), hsetup.2.2.2]
    exact h15
  have hrestoreNum := restoreControl_numeric rom B H (PA06A19PrepareControlBank017.controlBase N q t P)
    (by omega) (by omega) hCB_B copied (hcopySafe'.final _ _ _ _ _).1 hcopied15
  have hrestoreSafe : RunSafe B H rom allCode 2 copied := by
    rw [hcodeLast]
    exact straight_segment_safe rom B H lastLead restoreControl right restoreControl_noJump copied
      (by rw [hlast]; have hh := hcopied.2.1; rw [hlead] at hh; omega) hcopied.2.2 hrestoreNum
  have hfirst := RunSafe.add B H rom allCode 9
    (9 * PA06A19PrepareControlBank017.cacheLength N q + 4) state hsetupSafe
    (by rw [hsetupRun]; exact hcopySafe')
  have hfirstRun : natRun rom allCode (9 + (9 * PA06A19PrepareControlBank017.cacheLength N q + 4)) state = copied := by
    rw [natRun_add, hsetupRun]
  have hall := RunSafe.add B H rom allCode
    (9 + (9 * PA06A19PrepareControlBank017.cacheLength N q + 4)) 2 state hfirst
    (by rw [hfirstRun]; exact hrestoreSafe)
  convert hall using 1
  unfold transferClock
  omega

theorem actual_transfer_end_room (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    let t := treeSize q full
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
    let finish := PA06A19PrepareControlBank017.cacheBase full.length q t P +
      PA06A19PrepareControlBank017.cacheLength full.length q
    finish < PA06A19PrepareRuntimeHeader019.heapWords full.length q t ∧
      Fits (indexWidth 32 full.length q) finish := by
  dsimp only
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
  have hroom := PA06A19PrepareControlBank017.actual_cache_room full hq
  have hlen := PA06A19PrepareControlBank017.cacheLength_le_allowance full.length q
  have heq : PA06A19PrepareControlBank017.allocation full.length q t P =
      PA06A19PrepareRuntimeHeader019.heapWords full.length q t := by
    dsimp only [PA06A19PrepareControlBank017.allocation, PA06A19PrepareControlBank017.dimensions,
      PA06A19PrepareControlBank017.mass, PA06A19PrepareRuntimeHeader019.heapWords, P]
    omega
  constructor
  · rw [← heq]
    exact (Nat.add_le_add_left hlen _).trans_lt hroom.1
  · exact (Nat.add_le_add_left hlen _).trans_lt hroom.2

/-- Source words are an internal representation obligation. For an actual
incoming Word heap they hold pointwise without any extra caller premise. -/
theorem actual_transfer_safe (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hr : RegistersLE (2 ^ indexWidth 32 full.length q - 1) state)
    (hCB : state.register .address = PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
      (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)))
    (hM : state.heap 16 = PA06A19PrepareControlBank017.mass full.length q)
    (h15 : state.heap 15 = PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
      (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)))
    (hwords : ∀ position < PA06A19PrepareControlBank017.cacheLength full.length q,
      state.heap position ≤ 2 ^ indexWidth 32 full.length q - 1)
    (hpcB : 5 * (left ++ transfer left.length ++ right).length ≤ 2 ^ indexWidth 32 full.length q - 1) :
    RunSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) (left ++ transfer left.length ++ right) (transferClock full.length q) state := by
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
  let B := 2 ^ indexWidth 32 full.length q - 1
  let H := PA06A19PrepareRuntimeHeader019.heapWords full.length q t
  have hroom := actual_transfer_end_room q full hq
  have hd := PA06A19PrepareControlBank017.source_target_disjoint full.length q t P hq
  have htargetB : PA06A19PrepareControlBank017.cacheBase full.length q t P +
      PA06A19PrepareControlBank017.cacheLength full.length q ≤ B := by
    have hh := hroom.2
    change PA06A19PrepareControlBank017.cacheBase full.length q t P +
      PA06A19PrepareControlBank017.cacheLength full.length q < 2 ^ indexWidth 32 full.length q at hh
    dsimp only [B]
    omega
  exact transfer_safe full.length q t P hq (controllerInput q full used) B H
    ((by decide : 512 ≤ 8192).trans (maxWord_8192 full.length q hq))
    ((by decide : 17 ≤ 69).trans (PA06A19PrepareRuntimeHeader019.heapWords_room _ _ _))
    (by omega) (by have hh := hroom.1; change _ < H at hh; omega)
    htargetB hroom.1.le left right state hpc ha hr hCB hM h15 hwords hpcB

theorem transfer0_code_le : ∀ value ∈ packingCode (transfer 0), value ≤ 8192 := by decide

theorem transfer0_code_fit (N q : Nat) (hq : 0 < q) :
    WordsFit (indexWidth 32 N q) (packingCode (transfer 0)) := by
  intro value hv
  exact ((transfer0_code_le value hv).trans (maxWord_8192 N q hq)).trans_lt
    (PA17GeneratorStatic048.maxWord_fits _)

theorem transfer0_pc_le (N q : Nat) (hq : 0 < q) :
    5 * (transfer 0).length ≤ 2 ^ indexWidth 32 N q - 1 := by
  exact (by decide : 5 * (transfer 0).length ≤ 8192).trans (maxWord_8192 N q hq)

theorem transfer0_pc_fit (N q : Nat) (hq : 0 < q) :
    Fits (indexWidth 32 N q) (5 * (transfer 0).length) :=
  (transfer0_pc_le N q hq).trans_lt (PA17GeneratorStatic048.maxWord_fits _)

/-- The arbitrary actual Word heap supplies ALL copy-source word bounds.
No decoded heap, free source materialization or incoming RunSafe is used. -/
theorem actual_transfer_word (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false)
    (hCB : (state.register .address).toNat =
      PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
        (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)))
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = PA06A19PrepareControlBank017.mass full.length q)
    (h15 : (state.heap (BitVec.ofNat _ 15)).toNat =
      PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
        (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))) :
    packingRun (controllerInput q full used) (transfer 0) (transferClock full.length q) state =
      (natRun (controllerInput q full used) (transfer 0) (transferClock full.length q)
        (PA06A19PrepareRuntimeHeader019.natView state)).toWord (indexWidth 32 full.length q) := by
  let start := PA06A19PrepareRuntimeHeader019.natView state
  have hstartPC : start.pc = 5 * ([] : List PackingOp).length := by
    change state.pc.toNat = 0
    rw [hpc]
    rfl
  have hwords (position : Nat) (_hp : position < PA06A19PrepareControlBank017.cacheLength full.length q) :
      start.heap position ≤ 2 ^ indexWidth 32 full.length q - 1 := by
    have hh := (state.heap (BitVec.ofNat _ position)).toNat_lt_twoPow_of_le
      (Nat.le_refl (indexWidth 32 full.length q))
    change (state.heap (BitVec.ofNat _ position)).toNat ≤ _
    omega
  have hs := actual_transfer_safe q full used hq [] [] start hstartPC ha
    (PA06A19PrepareRuntimeHeader019.natView_registers state) hCB hM h15 hwords
    (by simpa only [List.nil_append, List.append_nil, List.length_nil] using transfer0_pc_le full.length q hq)
  have hs' : RunSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) (transfer 0) (transferClock full.length q) start := by
    simpa only [List.nil_append, List.append_nil, List.length_nil] using hs
  have hw := actual_word_run _ _ _ _ _ (transferClock full.length q) start hs'
    (PA17GeneratorStatic048.maxWord_fits _) (transfer0_code_fit full.length q hq)
    (transfer0_pc_fit full.length q hq) (transferClock full.length q) le_rfl
  simpa only [start, PA06A19PrepareRuntimeHeader019.natView_toWord] using hw

theorem actual_transfer_data (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false)
    (hCB : (state.register .address).toNat =
      PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
        (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)))
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = PA06A19PrepareControlBank017.mass full.length q)
    (h15 : (state.heap (BitVec.ofNat _ 15)).toNat =
      PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
        (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))) :
    let t := treeSize q full
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
    let fresh := packingRun (controllerInput q full used) (transfer 0) (transferClock full.length q) state
    fresh.halted = false ∧ fresh.pc.toNat = 110 ∧
    (fresh.register .address).toNat = PA06A19PrepareControlBank017.controlBase full.length q t P ∧
    ∀ address, fresh.heap address = BitVec.ofNat _
      (PA06A19PrepareControlBank017.relocatedHeap (PA06A19PrepareRuntimeHeader019.natView state).heap 0
        (PA06A19PrepareControlBank017.cacheBase full.length q t P)
        (PA06A19PrepareControlBank017.cacheLength full.length q) address.toNat) := by
  let bits := indexWidth 32 full.length q
  let start := PA06A19PrepareRuntimeHeader019.natView state
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
  have hn := transfer_run full.length q t P hq (controllerInput q full used) [] [] start
    (by change state.pc.toNat = 0; rw [hpc]; rfl) ha hCB hM h15
  have hn' :
      (natRun (controllerInput q full used) (transfer 0) (transferClock full.length q) start).register .address =
        PA06A19PrepareControlBank017.controlBase full.length q t P ∧
      (natRun (controllerInput q full used) (transfer 0) (transferClock full.length q) start).pc = 110 ∧
      (natRun (controllerInput q full used) (transfer 0) (transferClock full.length q) start).halted = false ∧
      (natRun (controllerInput q full used) (transfer 0) (transferClock full.length q) start).heap =
        PA06A19PrepareControlBank017.relocatedHeap start.heap 0
          (PA06A19PrepareControlBank017.cacheBase full.length q t P)
          (PA06A19PrepareControlBank017.cacheLength full.length q) := by
    simpa only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] using hn
  have hCBfit : Fits bits (PA06A19PrepareControlBank017.controlBase full.length q t P) := by
    simpa only [Nat.add_zero] using actual_bank_field_fits q full hq 0 (by decide)
  dsimp only
  simp only [actual_transfer_word q full used hq state hpc ha hCB hM h15]
  refine ⟨hn'.2.2.1, ?_, ?_, ?_⟩
  · change (BitVec.ofNat bits (natRun _ _ _ start).pc).toNat = 110
    rw [hn'.2.1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simpa only [transfer_length, AlgorithmClaims.Fits, bits] using transfer0_pc_fit full.length q hq)]
  · change (BitVec.ofNat bits ((natRun _ _ _ start).register .address)).toNat = _
    rw [hn'.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hCBfit]
  · intro address
    change BitVec.ofNat bits ((natRun _ _ _ start).heap address.toNat) = _
    rw [hn'.2.2.2]

theorem actual_transfer_frame (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false)
    (hCB : (state.register .address).toNat =
      PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
        (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)))
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = PA06A19PrepareControlBank017.mass full.length q)
    (h15 : (state.heap (BitVec.ofNat _ 15)).toNat =
      PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
        (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)))
    (address : BitVec (indexWidth 32 full.length q))
    (hout : address.toNat < PA06A19PrepareControlBank017.cacheBase full.length q (treeSize q full)
      (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))) :
    (packingRun (controllerInput q full used) (transfer 0) (transferClock full.length q) state).heap address = state.heap address := by
  have hd := (actual_transfer_data q full used hq state hpc ha hCB hM h15).2.2.2 address
  rw [hd, PA06A19PrepareControlBank017.relocatedHeap_frame _ _ _ _ address.toNat (Or.inl hout)]
  simp only [PA06A19PrepareRuntimeHeader019.natView, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026
