module

public import Structure.PA06_A19Prepare_RuntimeLayout026_Bank
public import Structure.PA06_A19Prepare_RuntimeLayout026_WordTransfer
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate: actual 47-op permanent-bank stores. The low slots are
internal outputs of layout and real relocation, not original input data.
This file bounds each short block, then transports the actual Word run. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PA17UniformGenerator035j PA17UniformGenerator035m
  PA17UniformGenerator035p

theorem lowToBank_low (source offset : Nat) (rom : PhysicalROM) (state : NatState)
    (hCB : 16 ≤ state.register .address) (low : Nat) (hlow : low ≤ 15) :
    (runOps rom (lowToBank source offset) state).heap low = state.heap low := by
  rw [lowToBank_heap]
  rw [Function.update_of_ne (show low ≠ state.register .address + offset by omega)]

theorem writeOldCapacity_low (rom : PhysicalROM) (state : NatState)
    (hCB : 16 ≤ state.register .address) (low : Nat) (hlow : low ≤ 15) :
    (runOps rom writeOldCapacity state).heap low = state.heap low := by
  rw [writeOldCapacity_heap]
  rw [Function.update_of_ne (show low ≠ state.register .address + 3 by omega)]

theorem lowToBank_numeric (source offset : Nat) (rom : PhysicalROM) (B H : Nat)
    (state : NatState) (hr : RegistersLE B state)
    (hsourceB : source ≤ B) (hsourceH : source < H)
    (htargetB : state.register .address + offset ≤ B) (htargetH : state.register .address + offset < H)
    (hvalue : state.heap source ≤ B) : NumericSafe B H rom (lowToBank source offset) state := by
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 5 at hc
    interval_cases count <;> cases register <;>
      simp +decide [lowToBank, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 5 at hc
    interval_cases count <;>
      simp +decide [lowToBank, runOps, natExecuteOp, Op.execute, Instruction.execute,
        NatAccessFits, AccessFits]
    all_goals omega

theorem writeOldCapacity_numeric (rom : PhysicalROM) (B H q t C : Nat)
    (hsmall : 8190 ≤ B) (hH : 13 ≤ H) (hqB : q ≤ B) (htB : t + 1 ≤ B)
    (hCB : C ≤ B) (hfactor : (t + 1) * 8190 ≤ B)
    (state : NatState) (hr : RegistersLE B state)
    (htargetB : state.register .address + 3 ≤ B) (htargetH : state.register .address + 3 < H)
    (hq : state.heap 10 = q) (ht : state.heap 11 = t) (hC : state.heap 12 = C) :
    NumericSafe B H rom writeOldCapacity state := by
  have hsub : C - q ≤ B := (Nat.sub_le _ _).trans hCB
  have hsub' : C - q - (t + 1) * 8190 ≤ B := (Nat.sub_le _ _).trans hsub
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 15 at hc
    interval_cases count <;> cases register <;>
      simp +decide [writeOldCapacity, runOps, natExecuteOp, natArithmetic, Op.execute,
        Instruction.execute, hq, ht, hC]
    all_goals omega
  · intro count hc
    change count < 15 at hc
    interval_cases count <;>
      simp +decide [writeOldCapacity, runOps, natExecuteOp, natArithmetic, Op.execute,
        Instruction.execute, NatAccessFits, AccessFits]
    all_goals omega

theorem writeIndexBase_numeric (rom : PhysicalROM) (B H P : Nat)
    (hsmall : 13 ≤ B) (hH : 14 ≤ H) (hP : P + 4 ≤ B)
    (state : NatState) (hr : RegistersLE B state)
    (htargetB : state.register .address + 6 ≤ B) (htargetH : state.register .address + 6 < H)
    (h13 : state.heap 13 = P) : NumericSafe B H rom writeIndexBase state := by
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 7 at hc
    interval_cases count <;> cases register <;>
      simp +decide [writeIndexBase, runOps, natExecuteOp, Op.execute, Instruction.execute, h13]
    all_goals omega
  · intro count hc
    change count < 7 at hc
    interval_cases count <;>
      simp +decide [writeIndexBase, runOps, natExecuteOp, Op.execute, Instruction.execute,
        NatAccessFits, AccessFits]
    all_goals omega

theorem bankSetup_numeric (rom : PhysicalROM) (B H N q t P : Nat)
    (hsmall : 8192 ≤ B) (hH : 16 ≤ H) (hN : N ≤ B) (hq : q ≤ B)
    (hC : capacityExpr N q t ≤ B) (hP : P + 4 ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hCB : 16 ≤ state.register .address)
    (htargetB : state.register .address + 6 ≤ B) (htargetH : state.register .address + 6 < H)
    (h9 : state.heap 9 = N) (h10 : state.heap 10 = q) (h11 : state.heap 11 = t)
    (h12 : state.heap 12 = capacityExpr N q t) (h13 : state.heap 13 = P) :
    NumericSafe B H rom bankSetup state := by
  let a := runOps rom (lowToBank 9 0) state
  let b := runOps rom (lowToBank 10 1) a
  let c := runOps rom (lowToBank 11 2) b
  let d := runOps rom writeOldCapacity c
  let e := runOps rom (lowToBank 12 4) d
  let f := runOps rom (lowToBank 13 5) e
  have haA : a.register .address = state.register .address := lowToBank_address 9 0 rom state
  have hbA : b.register .address = state.register .address := (lowToBank_address 10 1 rom a).trans haA
  have hcA : c.register .address = state.register .address := (lowToBank_address 11 2 rom b).trans hbA
  have hdA : d.register .address = state.register .address := (writeOldCapacity_address rom c).trans hcA
  have heA : e.register .address = state.register .address := (lowToBank_address 12 4 rom d).trans hdA
  have hfA : f.register .address = state.register .address := (lowToBank_address 13 5 rom e).trans heA
  have haL (low : Nat) (hl : low ≤ 15) : a.heap low = state.heap low := lowToBank_low 9 0 rom state hCB low hl
  have hbL (low : Nat) (hl : low ≤ 15) : b.heap low = state.heap low :=
    (lowToBank_low 10 1 rom a (by rw [haA]; exact hCB) low hl).trans (haL low hl)
  have hcL (low : Nat) (hl : low ≤ 15) : c.heap low = state.heap low :=
    (lowToBank_low 11 2 rom b (by rw [hbA]; exact hCB) low hl).trans (hbL low hl)
  have hdL (low : Nat) (hl : low ≤ 15) : d.heap low = state.heap low :=
    (writeOldCapacity_low rom c (by rw [hcA]; exact hCB) low hl).trans (hcL low hl)
  have heL (low : Nat) (hl : low ≤ 15) : e.heap low = state.heap low :=
    (lowToBank_low 12 4 rom d (by rw [hdA]; exact hCB) low hl).trans (hdL low hl)
  have hfL (low : Nat) (hl : low ≤ 15) : f.heap low = state.heap low :=
    (lowToBank_low 13 5 rom e (by rw [heA]; exact hCB) low hl).trans (heL low hl)
  have htB : t + 1 ≤ B := by unfold capacityExpr at hC; omega
  have hfactor : (t + 1) * 8190 ≤ B := by unfold capacityExpr at hC; omega
  have hs1 := lowToBank_numeric 9 0 rom B H state hr (by omega) (by omega)
    (by omega) (by omega) (by rw [h9]; exact hN)
  have hs2 := lowToBank_numeric 10 1 rom B H a (hs1.final _ _ _ _ _) (by omega) (by omega)
    (by rw [haA]; omega) (by rw [haA]; omega) (by rw [haL 10 (by decide), h10]; exact hq)
  have hs3 := lowToBank_numeric 11 2 rom B H b (hs2.final _ _ _ _ _) (by omega) (by omega)
    (by rw [hbA]; omega) (by rw [hbA]; omega) (by rw [hbL 11 (by decide), h11]; omega)
  have hs4 := writeOldCapacity_numeric rom B H q t (capacityExpr N q t) (by omega) (by omega)
    hq htB hC hfactor c (hs3.final _ _ _ _ _) (by rw [hcA]; omega) (by rw [hcA]; omega)
    ((hcL 10 (by decide)).trans h10) ((hcL 11 (by decide)).trans h11) ((hcL 12 (by decide)).trans h12)
  have hs5 := lowToBank_numeric 12 4 rom B H d (hs4.final _ _ _ _ _) (by omega) (by omega)
    (by rw [hdA]; omega) (by rw [hdA]; omega) (by rw [hdL 12 (by decide), h12]; exact hC)
  have hs6 := lowToBank_numeric 13 5 rom B H e (hs5.final _ _ _ _ _) (by omega) (by omega)
    (by rw [heA]; omega) (by rw [heA]; omega) (by rw [heL 13 (by decide), h13]; omega)
  have hs7 := writeIndexBase_numeric rom B H P (by omega) (by omega) hP f
    (hs6.final _ _ _ _ _) (by rw [hfA]; exact htargetB) (by rw [hfA]; exact htargetH)
    ((hfL 13 (by decide)).trans h13)
  have h12' := NumericSafe.append B H rom (lowToBank 9 0) (lowToBank 10 1) state hs1 hs2
  have h123 := NumericSafe.append B H rom _ (lowToBank 11 2) state h12' (by
    simpa only [runOps_append, a, b] using hs3)
  have h1234 := NumericSafe.append B H rom _ writeOldCapacity state h123 (by
    simpa only [runOps_append, a, b, c] using hs4)
  have h12345 := NumericSafe.append B H rom _ (lowToBank 12 4) state h1234 (by
    simpa only [runOps_append, a, b, c, d] using hs5)
  have h123456 := NumericSafe.append B H rom _ (lowToBank 13 5) state h12345 (by
    simpa only [runOps_append, a, b, c, d, e] using hs6)
  exact NumericSafe.append B H rom _ writeIndexBase state h123456 (by
    simpa only [runOps_append, a, b, c, d, e, f] using hs7)

theorem bankSetup_noJump : ∀ op ∈ bankSetup, NoJump op := by
  simp [bankSetup, lowToBank, writeOldCapacity, writeIndexBase, NoJump]

theorem actual_bankSetup_numeric (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : NatState) (hr : RegistersLE (2 ^ indexWidth 32 full.length q - 1) state)
    (hCB : state.register .address = PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
      (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)))
    (h9 : state.heap 9 = full.length) (h10 : state.heap 10 = q) (h11 : state.heap 11 = treeSize q full)
    (h12 : state.heap 12 = capacityExpr full.length q (treeSize q full))
    (h13 : state.heap 13 = packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) :
    NumericSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) bankSetup state := by
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  let B := 2 ^ indexWidth 32 full.length q - 1
  have hCB16 : 16 ≤ CB := by
    dsimp only [CB, PA06A19PrepareControlBank017.controlBase,
      PA06A19PrepareControlBank017.dimensions, PA06A19PrepareControlBank017.mass]
    omega
  have hCB6 := actual_bank_field_fits q full hq 6 (by decide)
  have hCB6B : CB + 6 ≤ B := by change CB + 6 < 2 ^ indexWidth 32 full.length q at hCB6; dsimp only [B]; omega
  have hCB6H : CB + 6 < PA06A19PrepareRuntimeHeader019.heapWords full.length q t := by
    have hh : PA06A19PrepareControlBank017.cacheBase full.length q t P +
        PA06A19PrepareControlBank017.cacheLength full.length q <
        PA06A19PrepareRuntimeHeader019.heapWords full.length q t := by
      simpa only [t, P] using (actual_transfer_end_room q full hq).1
    unfold PA06A19PrepareControlBank017.cacheBase at hh
    dsimp only [CB]
    omega
  have hP : P + 4 ≤ B := by
    dsimp only [CB, PA06A19PrepareControlBank017.controlBase] at hCB6B
    omega
  have hinput := PA17GeneratorStatic048.input_le_maxWord full.length q 0 hq (by omega)
  have hc := actual_capacity_fits q full hq
  exact bankSetup_numeric (controllerInput q full used) B _ full.length q t P
    (maxWord_8192 full.length q hq) (by exact (by decide : 16 ≤ 69).trans (PA06A19PrepareRuntimeHeader019.heapWords_room _ _ _))
    (by dsimp only [B]; omega) (by dsimp only [B]; omega)
    (by change capacityExpr full.length q t < 2 ^ indexWidth 32 full.length q at hc; dsimp only [B]; omega)
    hP state hr (by rw [hCB]; exact hCB16) (by rw [hCB]; exact hCB6B) (by rw [hCB]; exact hCB6H)
    h9 h10 h11 h12 h13

theorem bankSetup_safe (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hr : RegistersLE (2 ^ indexWidth 32 full.length q - 1) state)
    (hCB : state.register .address = PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
      (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)))
    (h9 : state.heap 9 = full.length) (h10 : state.heap 10 = q) (h11 : state.heap 11 = treeSize q full)
    (h12 : state.heap 12 = capacityExpr full.length q (treeSize q full))
    (h13 : state.heap 13 = packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) :
    RunSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) (left ++ bankSetup ++ right) 47 state :=
  straight_segment_safe _ _ _ left bankSetup right bankSetup_noJump state hpc ha
    (actual_bankSetup_numeric q full used hq state hr hCB h9 h10 h11 h12 h13)

theorem bankSetup_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ bankSetup ++ right) 47 state = runOps rom bankSetup state := by
  exact natRun_of_straight_segment rom (left ++ bankSetup ++ right) bankSetup left.length
    (by simp only [List.length_append]; omega) (PA17UniformGenerator035a.segment_index left bankSetup right)
    bankSetup_noJump state hpc ha

theorem bankSetup_code_le : ∀ value ∈ packingCode bankSetup, value ≤ 8192 := by decide

theorem bankSetup_code_fit (N q : Nat) (hq : 0 < q) :
    WordsFit (indexWidth 32 N q) (packingCode bankSetup) := by
  intro value hv
  exact ((bankSetup_code_le value hv).trans (maxWord_8192 N q hq)).trans_lt
    (PA17GeneratorStatic048.maxWord_fits _)

theorem bankSetup_pc_fit (N q : Nat) (hq : 0 < q) : Fits (indexWidth 32 N q) (5 * bankSetup.length) :=
  ((by decide : 5 * bankSetup.length ≤ 8192).trans (maxWord_8192 N q hq)).trans_lt
    (PA17GeneratorStatic048.maxWord_fits _)

/-- These low slots are internal outputs of the actual layout/copy chain.
The whole chain below must establish them; they are not new raw input. -/
theorem actual_bankSetup_word (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false)
    (hCB : (state.register .address).toNat = PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
      (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)))
    (h9 : (state.heap (BitVec.ofNat _ 9)).toNat = full.length)
    (h10 : (state.heap (BitVec.ofNat _ 10)).toNat = q)
    (h11 : (state.heap (BitVec.ofNat _ 11)).toNat = treeSize q full)
    (h12 : (state.heap (BitVec.ofNat _ 12)).toNat = capacityExpr full.length q (treeSize q full))
    (h13 : (state.heap (BitVec.ofNat _ 13)).toNat =
      packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) :
    packingRun (controllerInput q full used) bankSetup 47 state =
      (runOps (controllerInput q full used) bankSetup (PA06A19PrepareRuntimeHeader019.natView state)).toWord
        (indexWidth 32 full.length q) := by
  let start := PA06A19PrepareRuntimeHeader019.natView state
  have hstartPC : start.pc = 5 * ([] : List PackingOp).length := by
    change state.pc.toNat = 0
    rw [hpc]
    rfl
  have hs := bankSetup_safe q full used hq [] [] start hstartPC ha
    (PA06A19PrepareRuntimeHeader019.natView_registers state) hCB h9 h10 h11 h12 h13
  have hs' : RunSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) bankSetup 47 start := by
    simpa only [List.nil_append, List.append_nil] using hs
  have hw := actual_word_run _ _ _ _ _ 47 start hs' (PA17GeneratorStatic048.maxWord_fits _)
    (bankSetup_code_fit full.length q hq) (bankSetup_pc_fit full.length q hq) 47 le_rfl
  have hn : natRun (controllerInput q full used) bankSetup 47 start =
      runOps (controllerInput q full used) bankSetup start := by
    have hh := bankSetup_run (controllerInput q full used) [] [] start hstartPC ha
    simpa only [List.nil_append, List.append_nil] using hh
  simpa only [hn, start, PA06A19PrepareRuntimeHeader019.natView_toWord] using hw

private theorem bank_toWord_halted (bits : Nat) (natural : NatState) :
    (natural.toWord bits).halted = natural.halted := rfl

private theorem bank_toWord_pc (bits : Nat) (natural : NatState) :
    (natural.toWord bits).pc = BitVec.ofNat bits natural.pc := rfl

private theorem bank_toWord_register (bits : Nat) (natural : NatState) (reg : Register) :
    (natural.toWord bits).register reg = BitVec.ofNat bits (natural.register reg) := rfl

private theorem bank_toWord_heap (bits : Nat) (natural : NatState) (point : BitVec bits) :
    (natural.toWord bits).heap point = BitVec.ofNat bits (natural.heap point.toNat) := rfl

theorem actual_bankSetup_data (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false)
    (hCB : (state.register .address).toNat = PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
      (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)))
    (h9 : (state.heap (BitVec.ofNat _ 9)).toNat = full.length)
    (h10 : (state.heap (BitVec.ofNat _ 10)).toNat = q)
    (h11 : (state.heap (BitVec.ofNat _ 11)).toNat = treeSize q full)
    (h12 : (state.heap (BitVec.ofNat _ 12)).toNat = capacityExpr full.length q (treeSize q full))
    (h13 : (state.heap (BitVec.ofNat _ 13)).toNat =
      packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) :
    let t := treeSize q full
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
    let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
    let fresh := packingRun (controllerInput q full used) bankSetup 47 state
    fresh.halted = false ∧ fresh.pc.toNat = 235 ∧ (fresh.register .address).toNat = CB ∧
    ∀ address, fresh.heap address = BitVec.ofNat _
      (bankFields full.length q t P CB (PA06A19PrepareRuntimeHeader019.natView state).heap address.toNat) := by
  let bits := indexWidth 32 full.length q
  let start := PA06A19PrepareRuntimeHeader019.natView state
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  have hCB16 : 16 ≤ start.register .address := by
    change 16 ≤ (state.register .address).toNat
    rw [hCB]
    unfold PA06A19PrepareControlBank017.controlBase PA06A19PrepareControlBank017.dimensions
      PA06A19PrepareControlBank017.mass
    omega
  have hdata := bankSetup_heap (controllerInput q full used) start full.length q t P hCB16 h9 h10 h11 h12 h13
  have hCBA : start.register .address = CB := hCB
  have hCBfit : CB < 2 ^ bits := by
    dsimp only [CB, P, t, bits]
    simpa only [Nat.add_zero, AlgorithmClaims.Fits] using actual_bank_field_fits q full hq 0 (by decide)
  have he := actual_bankSetup_word q full used hq state hpc ha hCB h9 h10 h11 h12 h13
  have hhalt : (packingRun (controllerInput q full used) bankSetup 47 state).halted = false := by
    have hp := congrArg (fun s : WordState (indexWidth 32 full.length q) => s.halted) he
    rw [bank_toWord_halted, runOps_halted] at hp
    exact hp.trans ha
  have hspc : start.pc = 0 := by change state.pc.toNat = 0; rw [hpc]; rfl
  have hpNat : (runOps (controllerInput q full used) bankSetup start).pc = 235 := by
    rw [runOps_pc _ bankSetup start bankSetup_noJump, hspc, Nat.zero_add, bankSetup_length]
  have hpWord : (packingRun (controllerInput q full used) bankSetup 47 state).pc = BitVec.ofNat bits 235 := by
    have hp := congrArg (fun s : WordState (indexWidth 32 full.length q) => s.pc) he
    rw [bank_toWord_pc, hpNat] at hp
    exact hp
  have hpOut : (packingRun (controllerInput q full used) bankSetup 47 state).pc.toNat = 235 := by
    rw [hpWord, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simpa only [bankSetup_length, AlgorithmClaims.Fits, bits] using bankSetup_pc_fit full.length q hq)]
  have hAddrWord : (packingRun (controllerInput q full used) bankSetup 47 state).register .address = BitVec.ofNat bits CB := by
    have hp := congrArg (fun s : WordState (indexWidth 32 full.length q) => s.register .address) he
    rw [bank_toWord_register, bankSetup_address, hCBA] at hp
    exact hp
  have hAddr : ((packingRun (controllerInput q full used) bankSetup 47 state).register .address).toNat = CB := by
    rw [hAddrWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hCBfit]
  have hHeap : ∀ address : BitVec bits, (packingRun (controllerInput q full used) bankSetup 47 state).heap address = BitVec.ofNat bits
      (bankFields full.length q t P CB start.heap address.toNat) := by
    intro address
    have hp := congrFun (congrArg (fun s : WordState (indexWidth 32 full.length q) => s.heap) he) address
    rw [bank_toWord_heap, hdata, hCBA] at hp
    exact hp
  exact ⟨hhalt, hpOut, hAddr, hHeap⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026
