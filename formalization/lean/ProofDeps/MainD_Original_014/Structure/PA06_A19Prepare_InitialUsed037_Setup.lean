module

public import Structure.PA06_A19Prepare_InitialUsed037
public import PaperProofs.Structure.PA17_UniformGenerator_035p
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate actual33-op used-loop setup. All pointer/cursor/count inputs
are real permanent bank reads, and all control outputs are real stores. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PSTRBuildLower
  PA17UniformGenerator035j PA17UniformGenerator035m PA17UniformGenerator035p

theorem tableSetup_numeric (rom : PhysicalROM) (B H C q t : Nat)
    (hsmall : 8192 ≤ B) (hC : C ≤ B) (hq : q ≤ B) (ht : t + 1 ≤ B)
    (hfactor : 8192 * (t + 1) ≤ B)
    (state : NatState) (hr : RegistersLE B state)
    (hbankB : state.register .address + pointerSlot ≤ B)
    (hbankH : state.register .address + pointerSlot < H)
    (hCdata : state.heap (state.register .address + 4) = C)
    (hqdata : state.heap (state.register .address + 1) = q)
    (htdata : state.heap (state.register .address + 2) = t) :
    NumericSafe B H rom tableSetup state := by
  have hsub : C - q ≤ B := (Nat.sub_le _ _).trans hC
  have hsub' : C - q - 8192 * (t + 1) ≤ B := (Nat.sub_le _ _).trans hsub
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 18 at hc
    interval_cases count <;> cases register <;>
      simp +decide [tableSetup, relativeRead, relativeWrite, pointerSlot, runOps, natExecuteOp,
        natArithmetic, Op.execute, Instruction.execute, hCdata, hqdata, htdata]
    all_goals
      dsimp only [pointerSlot] at hbankB hbankH
      omega
  · intro count hc
    change count < 18 at hc
    interval_cases count <;>
      simp +decide [tableSetup, relativeRead, relativeWrite, pointerSlot, runOps, natExecuteOp,
        natArithmetic, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals
      dsimp only [pointerSlot] at hbankB hbankH
      omega

theorem cursorSetup_numeric (rom : PhysicalROM) (B H N q : Nat)
    (hsmall : 18 ≤ B) (hN : N ≤ B) (hq : q ≤ B) (hcursor : N * q + 2 ≤ B)
    (state : NatState) (hr : RegistersLE B state)
    (hbankB : state.register .address + counterSlot ≤ B)
    (hbankH : state.register .address + counterSlot < H)
    (hNdata : state.heap (state.register .address + 0) = N)
    (hqdata : state.heap (state.register .address + 1) = q) :
    NumericSafe B H rom cursorSetup state := by
  have hNread : state.heap (state.register .address) = N := by
    simpa only [Nat.add_zero] using hNdata
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 15 at hc
    interval_cases count <;> cases register <;>
      simp +decide [cursorSetup, relativeRead, relativeWrite, storeTotal, cursorSlot, counterSlot,
        runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute, hNread, hqdata]
    all_goals
      dsimp only [counterSlot] at hbankB hbankH
      omega
  · intro count hc
    change count < 15 at hc
    interval_cases count <;>
      simp +decide [cursorSetup, relativeRead, relativeWrite, storeTotal, cursorSlot, counterSlot,
        runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals
      dsimp only [counterSlot] at hbankB hbankH
      omega

theorem actual_control_room (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (offset : Nat) (hoffset : offset ≤ 511) :
    let t := treeSize q full
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
    let address := PA06A19PrepareControlBank017.controlBase full.length q t P + offset
    address < PA06A19PrepareRuntimeHeader019.heapWords full.length q t ∧ Fits (indexWidth 32 full.length q) address := by
  dsimp only
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
  have hs := PA06A19PrepareControlBank017.controls_cache_disjoint full.length q t P offset (by omega)
  have hr : PA06A19PrepareControlBank017.cacheBase full.length q t P +
      PA06A19PrepareControlBank017.cacheAllowance full.length q <
      PA06A19PrepareControlBank017.allocation full.length q t P :=
    (PA06A19PrepareControlBank017.actual_cache_room full hq).1
  have he : PA06A19PrepareControlBank017.allocation full.length q t P =
      PA06A19PrepareRuntimeHeader019.heapWords full.length q t := by
    dsimp only [PA06A19PrepareControlBank017.allocation, PA06A19PrepareControlBank017.dimensions,
      PA06A19PrepareControlBank017.mass, PA06A19PrepareRuntimeHeader019.heapWords, P]
    omega
  have hc : PA06A19PrepareControlBank017.controlBase full.length q t P + offset <
      PA06A19PrepareControlBank017.allocation full.length q t P := hs.trans ((Nat.le_add_right _ _).trans_lt hr)
  exact ⟨by rw [← he]; exact hc, hc.trans (PA06A19PrepareControlBank017.actual_allocation_fits full)⟩

theorem raw_end_le_capacity (N q t : Nat) (hq : 0 < q) :
    2 + N * q + q ≤ capacityWords 8192 N q t := by
  have hprod : N * q ≤ (N + 1) * (q + 2) := Nat.mul_le_mul (by omega) (by omega)
  have htable : (N + 1) * (q + 2) ≤ (N + 1) * (q + 2) * (t + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold capacityWords
  rw [ite_eq_right (Nat.ne_of_gt hq)]
  unfold tableWords cells
  omega

theorem actual_setup_numeric (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : NatState) (hr : RegistersLE (2 ^ indexWidth 32 full.length q - 1) state)
    (hcb : state.register .address = PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
      (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)))
    (hN : state.heap (state.register .address + 0) = full.length)
    (hQ : state.heap (state.register .address + 1) = q)
    (ht : state.heap (state.register .address + 2) = treeSize q full)
    (hC : state.heap (state.register .address + 4) = capacityWords 8192 full.length q (treeSize q full)) :
    NumericSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) setup state := by
  let rom := controllerInput q full used
  let t := treeSize q full
  let bits := indexWidth 32 full.length q
  let C := capacityWords 8192 full.length q t
  let P := packedCapacityWords q C bits
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  let B := 2 ^ bits - 1
  let H := PA06A19PrepareRuntimeHeader019.heapWords full.length q t
  let first := runOps rom tableSetup state
  have hcapacity := PA06A19PrepareRuntimeLayout026.actual_capacity_fits q full hq
  rw [PA06A19PrepareRuntimeLayout026.capacityExpr_eq _ _ _ hq] at hcapacity
  change C < 2 ^ bits at hcapacity
  have hCB : C ≤ B := by dsimp only [B]; omega
  have hCformula : C = tableWords full.length q t + q + 8192 * (t + 1) := by
    dsimp only [C, capacityWords]
    rw [ite_eq_right (Nat.ne_of_gt hq)]
  have hsmall : 8192 ≤ B := by rw [hCformula] at hCB; omega
  have htB : t + 1 ≤ B := by rw [hCformula] at hCB; omega
  have hfactor : 8192 * (t + 1) ≤ B := by rw [hCformula] at hCB; omega
  have hinput := PA17GeneratorStatic048.input_le_maxWord full.length q 0 hq (by omega)
  have hrawEnd := raw_end_le_capacity full.length q t hq
  have hroom16 := actual_control_room q full hq pointerSlot (by decide)
  have hroom18 := actual_control_room q full hq counterSlot (by decide)
  have hroom16B : CB + pointerSlot ≤ B := Nat.le_sub_one_of_lt hroom16.2
  have hroom18B : CB + counterSlot ≤ B := Nat.le_sub_one_of_lt hroom18.2
  have hs := tableSetup_numeric rom B H C q t hsmall hCB (by dsimp only [B, bits]; omega) htB hfactor state hr
    (by rw [hcb]; exact hroom16B)
    (by rw [hcb]; exact hroom16.1) hC hQ ht
  have hfirstA : first.register .address = state.register .address := tableSetup_address rom state
  have hfirstN : first.heap (first.register .address + 0) = full.length := by
    rw [tableSetup_heap, hfirstA, Function.update_of_ne (by dsimp only [pointerSlot]; omega)]
    exact hN
  have hfirstQ : first.heap (first.register .address + 1) = q := by
    rw [tableSetup_heap, hfirstA, Function.update_of_ne (by dsimp only [pointerSlot]; omega)]
    exact hQ
  have hlater := cursorSetup_numeric rom B H full.length q (by omega)
    (by dsimp only [B, bits]; omega) (by dsimp only [B, bits]; omega) (by omega) first (hs.final _ _ _ _ _)
    (by rw [hfirstA, hcb]; exact hroom18B)
    (by rw [hfirstA, hcb]; exact hroom18.1) hfirstN hfirstQ
  exact NumericSafe.append B H rom tableSetup cursorSetup state hs hlater

structure BankData (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (indexWidth 32 full.length q)) : Prop where
  base : (state.register .address).toNat = PA06A19PrepareControlBank017.controlBase full.length q
    (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))
  N : (state.heap (BitVec.ofNat _ (PA06A19PrepareControlBank017.controlBase full.length q
    (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) + 0))).toNat = full.length
  Q : (state.heap (BitVec.ofNat _ (PA06A19PrepareControlBank017.controlBase full.length q
    (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) + 1))).toNat = q
  T : (state.heap (BitVec.ofNat _ (PA06A19PrepareControlBank017.controlBase full.length q
    (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) + 2))).toNat = treeSize q full
  C : (state.heap (BitVec.ofNat _ (PA06A19PrepareControlBank017.controlBase full.length q
    (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) + 4))).toNat =
      capacityWords 8192 full.length q (treeSize q full)

theorem bank_natView (q : Nat) (full : List (Finset (Fin q)))
    (before : WordState (indexWidth 32 full.length q)) (hd : BankData q full before) :
    let start := PA06A19PrepareRuntimeHeader019.natView before
    start.heap (start.register .address + 0) = full.length ∧ start.heap (start.register .address + 1) = q ∧
    start.heap (start.register .address + 2) = treeSize q full ∧
    start.heap (start.register .address + 4) = capacityWords 8192 full.length q (treeSize q full) := by
  dsimp only [PA06A19PrepareRuntimeHeader019.natView]
  simp only [hd.base]
  exact ⟨hd.N, hd.Q, hd.T, hd.C⟩

theorem setup_word (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false) (hd : BankData q full before)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ setup ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ setup ++ right).length)) :
    packingRun (controllerInput q full used) (left ++ setup ++ right) 33 before =
      (runOps (controllerInput q full used) setup (PA06A19PrepareRuntimeHeader019.natView before)).toWord (indexWidth 32 full.length q) := by
  have hdata := bank_natView q full before hd
  have hs0 := straight_segment_safe _ _ _ left setup right setup_noJump _ hpc ha
    (actual_setup_numeric q full used hq _ (PA06A19PrepareRuntimeHeader019.natView_registers before)
      hd.base hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2)
  have hs : RunSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) (left ++ setup ++ right) 33 (PA06A19PrepareRuntimeHeader019.natView before) := by
    simpa only [setup_length] using hs0
  have hw := actual_word_run _ _ _ _ _ 33 _ hs (PA17GeneratorStatic048.maxWord_fits _) hcode hpcCode 33 le_rfl
  have hn : natRun (controllerInput q full used) (left ++ setup ++ right) 33 (PA06A19PrepareRuntimeHeader019.natView before) =
      runOps (controllerInput q full used) setup (PA06A19PrepareRuntimeHeader019.natView before) := by
    have hn0 := natRun_of_straight_segment (controllerInput q full used) (left ++ setup ++ right) setup left.length
      (by simp only [List.length_append]; omega)
      (PA17UniformGenerator035a.segment_index left setup right) setup_noJump
      (PA06A19PrepareRuntimeHeader019.natView before) hpc ha
    simpa only [setup_length] using hn0
  simpa only [hn, PA06A19PrepareRuntimeHeader019.natView_toWord] using hw

theorem setup_prefix_access (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false) (hd : BankData q full before)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ setup ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ setup ++ right).length)) (count : Nat) (hc : count < 33) :
    let code := left ++ setup ++ right
    let actual := packingRun (controllerInput q full used) code count before
    actual.halted = false ∧ actual.pc.toNat + 4 < (packingCode code).length ∧
    let fetched := physicalFetch (indexWidth 32 full.length q) (packingCode code) actual.pc.toNat
    ∃ op, PackingOp.decode fetched = some op ∧ packingAccessFits (controllerInput q full used)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)) actual op := by
  have hdata := bank_natView q full before hd
  have hs0 := straight_segment_safe _ _ _ left setup right setup_noJump _ hpc ha
    (actual_setup_numeric q full used hq _ (PA06A19PrepareRuntimeHeader019.natView_registers before)
      hd.base hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2)
  have hs : RunSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) (left ++ setup ++ right) 33 (PA06A19PrepareRuntimeHeader019.natView before) := by
    simpa only [setup_length] using hs0
  have hw := actual_word_fetch_access _ _ _ _ _ 33 _ hs
    (PA17GeneratorStatic048.maxWord_fits _) hcode hpcCode count hc
  simpa only [PA06A19PrepareRuntimeHeader019.natView_toWord] using hw

theorem setup_word_heap (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false) (hd : BankData q full before)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ setup ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ setup ++ right).length)) :
    let CB := (before.register .address).toNat
    let natural := PA06A19PrepareRuntimeHeader019.natView before
    let heap := Function.update (Function.update (Function.update natural.heap
      (CB + pointerSlot) (tableWords full.length q (treeSize q full)))
      (CB + cursorSlot) (2 + full.length * q)) (CB + counterSlot) q
    ∀ point, (packingRun (controllerInput q full used) (left ++ setup ++ right) 33 before).heap point =
      BitVec.ofNat _ (heap point.toNat) := by
  have hdata := bank_natView q full before hd
  have hh := setup_heap q full used hq (PA06A19PrepareRuntimeHeader019.natView before)
    (before.register .address).toNat rfl hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2
  dsimp only
  intro point
  rw [setup_word q full used hq left right before hpc ha hd hcode hpcCode]
  change BitVec.ofNat _ ((runOps _ setup (PA06A19PrepareRuntimeHeader019.natView before)).heap point.toNat) = _
  rw [hh]

theorem setup_word_frame (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false) (hd : BankData q full before)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ setup ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ setup ++ right).length))
    (point : BitVec (indexWidth 32 full.length q))
    (hne : point.toNat ≠ (before.register .address).toNat + pointerSlot ∧
      point.toNat ≠ (before.register .address).toNat + cursorSlot ∧
      point.toNat ≠ (before.register .address).toNat + counterSlot) :
    (packingRun (controllerInput q full used) (left ++ setup ++ right) 33 before).heap point = before.heap point := by
  rw [setup_word_heap q full used hq left right before hpc ha hd hcode hpcCode point]
  simp only [Function.update_of_ne hne.2.2, Function.update_of_ne hne.2.1, Function.update_of_ne hne.1]
  simp only [PA06A19PrepareRuntimeHeader019.natView, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem setup_toWord_halted (bits : Nat) (state : NatState) :
    (state.toWord bits).halted = state.halted := rfl

private theorem setup_toWord_pc (bits : Nat) (state : NatState) :
    (state.toWord bits).pc = BitVec.ofNat bits state.pc := rfl

private theorem setup_toWord_register (bits : Nat) (state : NatState) (reg : Register) :
    (state.toWord bits).register reg = BitVec.ofNat bits (state.register reg) := rfl

theorem setup_word_control (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false) (hd : BankData q full before)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ setup ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ setup ++ right).length)) :
    let after := packingRun (controllerInput q full used) (left ++ setup ++ right) 33 before
    after.halted = false ∧ after.pc.toNat = 5 * (left.length + 33) ∧ after.register .address = before.register .address := by
  have he := setup_word q full used hq left right before hpc ha hd hcode hpcCode
  have hhalt : (packingRun (controllerInput q full used) (left ++ setup ++ right) 33 before).halted = false := by
    have hp := congrArg (fun s : WordState (indexWidth 32 full.length q) => s.halted) he
    rw [setup_toWord_halted, runOps_halted] at hp
    exact hp.trans ha
  have hpNat : (runOps (controllerInput q full used) setup
      (PA06A19PrepareRuntimeHeader019.natView before)).pc = 5 * (left.length + 33) := by
    rw [runOps_pc _ setup _ setup_noJump, setup_length]
    change before.pc.toNat + 5 * 33 = _
    omega
  have hpcWord : (packingRun (controllerInput q full used) (left ++ setup ++ right) 33 before).pc =
      BitVec.ofNat (indexWidth 32 full.length q) (5 * (left.length + 33)) := by
    have hp := congrArg (fun s : WordState (indexWidth 32 full.length q) => s.pc) he
    rw [setup_toWord_pc, hpNat] at hp
    exact hp
  have hpcNat : (packingRun (controllerInput q full used) (left ++ setup ++ right) 33 before).pc.toNat =
      5 * (left.length + 33) := by
    rw [hpcWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((by
      simp only [List.length_append, setup_length]
      omega : 5 * (left.length + 33) ≤ 5 * (left ++ setup ++ right).length).trans_lt hpcCode)]
  have haddress : (packingRun (controllerInput q full used) (left ++ setup ++ right) 33 before).register .address =
      before.register .address := by
    have hp := congrArg (fun s : WordState (indexWidth 32 full.length q) => s.register .address) he
    rw [setup_toWord_register, setup_address] at hp
    simpa only [PA06A19PrepareRuntimeHeader019.natView, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hp
  exact ⟨hhalt, hpcNat, haddress⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037
