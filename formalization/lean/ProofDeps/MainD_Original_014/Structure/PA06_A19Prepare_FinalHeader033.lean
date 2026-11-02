module

public import Structure.PA06_A19Prepare_RuntimeLayout026_Bounds
public import Structure.PA06_A19Prepare_PackedView013
public import PaperProofs.Structure.PA17_UniformGenerator_035p
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate: execute ONLY after DP and initial-used stores. Temporary
header3 is really read; bank2/4/5 are really loaded, physical0/1/2 are really
stored, and ordinary stage/failed are really zeroed. The tempHeader is not
identified with the final live representation. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFinalHeader033

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PA17UniformGenerator035j PA17UniformGenerator035m
  PA17UniformGenerator035p

def readBits : List PackingOp :=
  [.base (.base (.constant .index 3)), .base (.base (.loadHeap .old .index))]

def bankToHeader (source target : Nat) : List PackingOp :=
  [.base (.base (.constant .index source)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .total .index)), .base (.base (.constant .index target)),
   .base (.base (.storeHeap .index .total))]

def zeroStageFailed : List PackingOp :=
  [.base (.base (.constant .fresh 4)), .base (.base (.add .index .total .fresh)),
   .base (.base (.constant .value 0)), .base (.base (.storeHeap .index .value)),
   .base (.base (.constant .fresh 1)), .base (.base (.add .index .index .fresh)),
   .base (.base (.storeHeap .index .value))]

def program : List PackingOp := readBits ++ bankToHeader 2 0 ++ bankToHeader 4 1 ++ bankToHeader 5 2 ++ zeroStageFailed

theorem program_length : program.length = 24 := rfl
theorem program_noJump : ∀ op ∈ program, NoJump op := by
  simp [program, readBits, bankToHeader, zeroStageFailed, NoJump]

def finalHeap (t C P : Nat) (heap : Nat → Nat) : Nat → Nat :=
  Function.update (Function.update (Function.update (Function.update (Function.update heap 0 t) 1 C) 2 P) (P + 4) 0) (P + 5) 0

theorem readBits_heap (rom : PhysicalROM) (state : NatState) : (runOps rom readBits state).heap = state.heap := rfl
theorem readBits_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom readBits state).register .address = state.register .address := rfl
theorem bankToHeader_heap (source target : Nat) (rom : PhysicalROM) (state : NatState) :
    (runOps rom (bankToHeader source target) state).heap =
      Function.update state.heap target (state.heap (state.register .address + source)) := rfl
theorem bankToHeader_address (source target : Nat) (rom : PhysicalROM) (state : NatState) :
    (runOps rom (bankToHeader source target) state).register .address = state.register .address := rfl
theorem bankToHeader_total (source target : Nat) (rom : PhysicalROM) (state : NatState) :
    (runOps rom (bankToHeader source target) state).register .total = state.heap (state.register .address + source) := rfl
theorem zeroStageFailed_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom zeroStageFailed state).heap = Function.update
      (Function.update state.heap (state.register .total + 4) 0) (state.register .total + 5) 0 := by
  simp +decide only [zeroStageFailed, runOps, natExecuteOp, Op.execute, Instruction.execute,
    Function.update_apply, ↓reduceIte, Nat.add_assoc]
theorem zeroStageFailed_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom zeroStageFailed state).register .address = state.register .address := rfl

theorem program_heap (rom : PhysicalROM) (state : NatState) (t C P : Nat)
    (hCB : 16 ≤ state.register .address)
    (ht : state.heap (state.register .address + 2) = t)
    (hC : state.heap (state.register .address + 4) = C)
    (hP : state.heap (state.register .address + 5) = P) :
    (runOps rom program state).heap = finalHeap t C P state.heap := by
  have hne0 (offset : Nat) : state.register .address + offset ≠ 0 := by omega
  have hne1 (offset : Nat) : state.register .address + offset ≠ 1 := by omega
  simp only [program, runOps_append, zeroStageFailed_heap, bankToHeader_heap,
    bankToHeader_total, bankToHeader_address, readBits_heap, readBits_address]
  simp only [finalHeap, Function.update_apply, hne0, hne1, ite_false, ht, hC, hP]

theorem program_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom program state).register .address = state.register .address := by
  simp only [program, runOps_append, zeroStageFailed_address, bankToHeader_address, readBits_address]

theorem readBits_numeric (rom : PhysicalROM) (B H : Nat) (hsmall : 3 ≤ B) (hH : 4 ≤ H)
    (state : NatState) (hr : RegistersLE B state) (hbits : state.heap 3 ≤ B) :
    NumericSafe B H rom readBits state := by
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 2 at hc
    interval_cases count <;> cases register <;>
      simp +decide [readBits, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 2 at hc
    interval_cases count <;>
      simp +decide [readBits, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals omega

theorem bankToHeader_numeric (source target : Nat) (rom : PhysicalROM) (B H : Nat)
    (state : NatState) (hr : RegistersLE B state)
    (hsourceB : state.register .address + source ≤ B) (hsourceH : state.register .address + source < H)
    (htargetB : target ≤ B) (htargetH : target < H)
    (hvalue : state.heap (state.register .address + source) ≤ B) :
    NumericSafe B H rom (bankToHeader source target) state := by
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 5 at hc
    interval_cases count <;> cases register <;>
      simp +decide [bankToHeader, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 5 at hc
    interval_cases count <;>
      simp +decide [bankToHeader, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals omega

theorem zeroStageFailed_numeric (rom : PhysicalROM) (B H P : Nat)
    (hsmall : 4 ≤ B) (hendB : P + 5 ≤ B) (hendH : P + 5 < H)
    (state : NatState) (hr : RegistersLE B state) (hP : state.register .total = P) :
    NumericSafe B H rom zeroStageFailed state := by
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 7 at hc
    interval_cases count <;> cases register <;>
      simp +decide [zeroStageFailed, runOps, natExecuteOp, Op.execute, Instruction.execute, hP]
    all_goals omega
  · intro count hc
    change count < 7 at hc
    interval_cases count <;>
      simp +decide [zeroStageFailed, runOps, natExecuteOp, Op.execute, Instruction.execute,
        NatAccessFits, AccessFits, hP]
    all_goals omega

theorem program_numeric (rom : PhysicalROM) (B H t C P bits : Nat)
    (hsmall : 5 ≤ B) (hH : 4 ≤ H) (htB : t ≤ B) (hCB : C ≤ B) (hPB : P ≤ B) (hbB : bits ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hbase : 16 ≤ state.register .address)
    (hbankB : state.register .address + 5 ≤ B) (hbankH : state.register .address + 5 < H)
    (hstageB : P + 5 ≤ B) (hstageH : P + 5 < H)
    (ht : state.heap (state.register .address + 2) = t)
    (hC : state.heap (state.register .address + 4) = C)
    (hP : state.heap (state.register .address + 5) = P) (hb : state.heap 3 = bits) :
    NumericSafe B H rom program state := by
  let a := runOps rom readBits state
  let b := runOps rom (bankToHeader 2 0) a
  let c := runOps rom (bankToHeader 4 1) b
  let d := runOps rom (bankToHeader 5 2) c
  have haA : a.register .address = state.register .address := readBits_address rom state
  have hbA : b.register .address = state.register .address := (bankToHeader_address 2 0 rom a).trans haA
  have hcA : c.register .address = state.register .address := (bankToHeader_address 4 1 rom b).trans hbA
  have haH : a.heap = state.heap := readBits_heap rom state
  have hb4 : b.heap (b.register .address + 4) = C := by
    rw [bankToHeader_heap, hbA, haA, haH, Function.update_of_ne (by omega : state.register .address + 4 ≠ 0)]
    exact hC
  have hc5 : c.heap (c.register .address + 5) = P := by
    rw [bankToHeader_heap, hcA, hbA, Function.update_of_ne (by omega : state.register .address + 5 ≠ 1),
      bankToHeader_heap, haA, haH, Function.update_of_ne (by omega : state.register .address + 5 ≠ 0)]
    exact hP
  have hdP : d.register .total = P := (bankToHeader_total 5 2 rom c).trans hc5
  have hs1 := readBits_numeric rom B H (by omega) hH state hr (by rw [hb]; exact hbB)
  have hs2 := bankToHeader_numeric 2 0 rom B H a (hs1.final _ _ _ _ _)
    (by rw [haA]; omega) (by rw [haA]; omega) (by omega) (by omega)
    (by rw [haA, haH, ht]; exact htB)
  have hs3 := bankToHeader_numeric 4 1 rom B H b (hs2.final _ _ _ _ _)
    (by rw [hbA]; omega) (by rw [hbA]; omega) (by omega) (by omega) (by rw [hb4]; exact hCB)
  have hs4 := bankToHeader_numeric 5 2 rom B H c (hs3.final _ _ _ _ _)
    (by rw [hcA]; exact hbankB) (by rw [hcA]; exact hbankH) (by omega) (by omega) (by rw [hc5]; exact hPB)
  have hs5 := zeroStageFailed_numeric rom B H P (by omega) hstageB hstageH d (hs4.final _ _ _ _ _) hdP
  have h12 := NumericSafe.append B H rom readBits (bankToHeader 2 0) state hs1 hs2
  have h123 := NumericSafe.append B H rom _ (bankToHeader 4 1) state h12 (by
    simpa only [runOps_append, a, b] using hs3)
  have h1234 := NumericSafe.append B H rom _ (bankToHeader 5 2) state h123 (by
    simpa only [runOps_append, a, b, c] using hs4)
  exact NumericSafe.append B H rom _ zeroStageFailed state h1234 (by
    simpa only [runOps_append, a, b, c, d] using hs5)

theorem actual_numeric (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : NatState) (hr : RegistersLE (2 ^ indexWidth 32 full.length q - 1) state)
    (hcb : state.register .address = PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
      (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)))
    (ht : state.heap (state.register .address + 2) = treeSize q full)
    (hC : state.heap (state.register .address + 4) = capacityWords 8192 full.length q (treeSize q full))
    (hP : state.heap (state.register .address + 5) = packedCapacityWords q
      (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))
    (hb : state.heap 3 = indexWidth 32 full.length q) :
    NumericSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) program state := by
  let t := treeSize q full
  let bits := indexWidth 32 full.length q
  let C := capacityWords 8192 full.length q t
  let P := packedCapacityWords q C bits
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  let B := 2 ^ bits - 1
  let H := PA06A19PrepareRuntimeHeader019.heapWords full.length q t
  have hbase : 16 ≤ CB := by
    dsimp only [CB, PA06A19PrepareControlBank017.controlBase,
      PA06A19PrepareControlBank017.dimensions, PA06A19PrepareControlBank017.mass]
    omega
  have hstage : P + 5 < CB := by
    dsimp only [CB, PA06A19PrepareControlBank017.controlBase,
      PA06A19PrepareControlBank017.dimensions, PA06A19PrepareControlBank017.mass]
    omega
  have hfit := PA06A19PrepareRuntimeLayout026.actual_bank_field_fits q full hq 5 (by decide)
  have hbankB : CB + 5 ≤ B := by
    change CB + 5 < 2 ^ bits at hfit
    dsimp only [B]
    omega
  have hbankH : CB + 5 < H := by
    have hs := PA06A19PrepareControlBank017.controls_cache_disjoint full.length q t P 5 (by decide)
    have hh : PA06A19PrepareControlBank017.cacheBase full.length q t P +
        PA06A19PrepareControlBank017.cacheAllowance full.length q <
        PA06A19PrepareControlBank017.allocation full.length q t P :=
      (PA06A19PrepareControlBank017.actual_cache_room full hq).1
    have he : PA06A19PrepareControlBank017.allocation full.length q t P = H := by
      dsimp only [PA06A19PrepareControlBank017.allocation, PA06A19PrepareControlBank017.dimensions,
        PA06A19PrepareControlBank017.mass, H, PA06A19PrepareRuntimeHeader019.heapWords, P, C, bits]
      omega
    rw [he] at hh
    exact hs.trans ((Nat.le_add_right _ _).trans_lt hh)
  have hsmall := PA06A19PrepareRuntimeHeader019.maxWord_small full.length q hq
  have hinput := PA17GeneratorStatic048.input_le_maxWord full.length q 0 hq (by omega)
  have htree := PA06A19PrepareControlBank017.treeSize_bound full
  have hbits := PA17GeneratorStatic048.bits_le_maxWord full.length q 0 hq (by omega)
  have hc := PA06A19PrepareRuntimeLayout026.actual_capacity_fits q full hq
  rw [PA06A19PrepareRuntimeLayout026.capacityExpr_eq _ _ _ hq] at hc
  change C < 2 ^ bits at hc
  have hp := PA06A19PrepareRuntimeLayout026.actual_packed_fits q full hq
  rw [PA06A19PrepareRuntimeLayout026.capacityExpr_eq _ _ _ hq] at hp
  change P < 2 ^ bits at hp
  apply program_numeric (controllerInput q full used) B H t C P bits
    (by dsimp only [B, bits]; omega) ((by decide : 4 ≤ 69).trans (PA06A19PrepareRuntimeHeader019.heapWords_room _ _ _))
    (by dsimp only [B, bits, t]; omega) (by dsimp only [B]; omega)
    (by dsimp only [B]; omega) hbits state hr
    (by rw [hcb]; exact hbase) (by rw [hcb]; exact hbankB) (by rw [hcb]; exact hbankH)
    (by omega) (by omega) ht hC hP hb

structure BankData (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (indexWidth 32 full.length q)) : Prop where
  base : (state.register .address).toNat = PA06A19PrepareControlBank017.controlBase full.length q
    (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))
  T : (state.heap (BitVec.ofNat _ (PA06A19PrepareControlBank017.controlBase full.length q
    (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) + 2))).toNat = treeSize q full
  C : (state.heap (BitVec.ofNat _ (PA06A19PrepareControlBank017.controlBase full.length q
    (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) + 4))).toNat =
      capacityWords 8192 full.length q (treeSize q full)
  P : (state.heap (BitVec.ofNat _ (PA06A19PrepareControlBank017.controlBase full.length q
    (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) + 5))).toNat =
      packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)

theorem input_natView (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (before : WordState (indexWidth 32 full.length q)) (hbank : BankData q full before)
    (hh : PA06A19PrepareRuntimePacked016.Header q before.heap) :
    let start := PA06A19PrepareRuntimeHeader019.natView before
    start.heap (start.register .address + 2) = treeSize q full ∧
    start.heap (start.register .address + 4) = capacityWords 8192 full.length q (treeSize q full) ∧
    start.heap (start.register .address + 5) = packedCapacityWords q
      (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) ∧
    start.heap 3 = indexWidth 32 full.length q := by
  have hbits := PA17GeneratorStatic048.bits_le_maxWord full.length q 0 hq (by omega)
  have hb := hbits.trans_lt (PA17GeneratorStatic048.maxWord_fits _)
  dsimp only [PA06A19PrepareRuntimeHeader019.natView]
  simp only [hbank.base]
  refine ⟨hbank.T, hbank.C, hbank.P, ?_⟩
  rw [hh.wordBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

theorem actual_safe (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hbank : BankData q full before) (hh : PA06A19PrepareRuntimePacked016.Header q before.heap) :
    RunSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) (left ++ program ++ right) 24 (PA06A19PrepareRuntimeHeader019.natView before) := by
  have hd := input_natView q full hq before hbank hh
  exact straight_segment_safe _ _ _ left program right program_noJump _ hpc ha
    (actual_numeric q full used hq _ (PA06A19PrepareRuntimeHeader019.natView_registers before)
      hbank.base hd.1 hd.2.1 hd.2.2.1 hd.2.2.2)

theorem actual_word (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hbank : BankData q full before) (hh : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ program ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ program ++ right).length)) :
    packingRun (controllerInput q full used) (left ++ program ++ right) 24 before =
      (runOps (controllerInput q full used) program (PA06A19PrepareRuntimeHeader019.natView before)).toWord
        (indexWidth 32 full.length q) := by
  have hs := actual_safe q full used hq left right before hpc ha hbank hh
  have hw := actual_word_run _ _ _ _ _ 24 _ hs (PA17GeneratorStatic048.maxWord_fits _) hcode hpcCode 24 le_rfl
  have hn := natRun_of_straight_segment (controllerInput q full used) (left ++ program ++ right) program left.length
    (by simp only [List.length_append]; omega) (PA17UniformGenerator035a.segment_index left program right)
    program_noJump (PA06A19PrepareRuntimeHeader019.natView before) hpc ha
  have hn' : natRun (controllerInput q full used) (left ++ program ++ right) 24
      (PA06A19PrepareRuntimeHeader019.natView before) =
      runOps (controllerInput q full used) program (PA06A19PrepareRuntimeHeader019.natView before) := hn
  simpa only [hn', PA06A19PrepareRuntimeHeader019.natView_toWord] using hw

theorem actual_prefix_access (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hbank : BankData q full before) (hh : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ program ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ program ++ right).length))
    (count : Nat) (hc : count < 24) :
    let code := left ++ program ++ right
    let actual := packingRun (controllerInput q full used) code count before
    actual.halted = false ∧ actual.pc.toNat + 4 < (packingCode code).length ∧
    let fetched := physicalFetch (indexWidth 32 full.length q) (packingCode code) actual.pc.toNat
    ∃ op, PackingOp.decode fetched = some op ∧ packingAccessFits (controllerInput q full used)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)) actual op := by
  have hs := actual_safe q full used hq left right before hpc ha hbank hh
  have hw := actual_word_fetch_access _ _ _ _ _ 24 _ hs
    (PA17GeneratorStatic048.maxWord_fits _) hcode hpcCode count hc
  simpa only [PA06A19PrepareRuntimeHeader019.natView_toWord] using hw

theorem finalHeap_values (t C P : Nat) (heap : Nat → Nat) :
    finalHeap t C P heap 0 = t ∧ finalHeap t C P heap 1 = C ∧ finalHeap t C P heap 2 = P ∧
    finalHeap t C P heap 3 = heap 3 ∧ finalHeap t C P heap (P + 4) = 0 ∧ finalHeap t C P heap (P + 5) = 0 := by
  simp (disch := omega) [finalHeap]

theorem actual_heap (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hbank : BankData q full before) (hh : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ program ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ program ++ right).length)) :
    let t := treeSize q full
    let C := capacityWords 8192 full.length q t
    let P := packedCapacityWords q C (indexWidth 32 full.length q)
    ∀ point, (packingRun (controllerInput q full used) (left ++ program ++ right) 24 before).heap point =
      BitVec.ofNat _ (finalHeap t C P (PA06A19PrepareRuntimeHeader019.natView before).heap point.toNat) := by
  have hd := input_natView q full hq before hbank hh
  have hbase : 16 ≤ (PA06A19PrepareRuntimeHeader019.natView before).register .address := by
    change 16 ≤ (before.register .address).toNat
    rw [hbank.base]
    unfold PA06A19PrepareControlBank017.controlBase PA06A19PrepareControlBank017.dimensions PA06A19PrepareControlBank017.mass
    omega
  dsimp only
  intro point
  rw [actual_word q full used hq left right before hpc ha hbank hh hcode hpcCode]
  change BitVec.ofNat _ ((runOps _ program (PA06A19PrepareRuntimeHeader019.natView before)).heap point.toNat) = _
  rw [program_heap _ _ _ _ _ hbase hd.1 hd.2.1 hd.2.2.1]

private theorem word_halted (bits : Nat) (state : NatState) : (state.toWord bits).halted = state.halted := rfl
private theorem word_pc (bits : Nat) (state : NatState) : (state.toWord bits).pc = BitVec.ofNat bits state.pc := rfl
private theorem word_register (bits : Nat) (state : NatState) (reg : Register) :
    (state.toWord bits).register reg = BitVec.ofNat bits (state.register reg) := rfl

theorem actual_control (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hbank : BankData q full before) (hh : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ program ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ program ++ right).length)) :
    let after := packingRun (controllerInput q full used) (left ++ program ++ right) 24 before
    after.halted = false ∧ after.pc.toNat = 5 * (left.length + 24) ∧
      after.register .address = before.register .address := by
  have he := actual_word q full used hq left right before hpc ha hbank hh hcode hpcCode
  have hhalt : (packingRun (controllerInput q full used) (left ++ program ++ right) 24 before).halted = false := by
    have hp := congrArg (fun s : WordState (indexWidth 32 full.length q) => s.halted) he
    rw [word_halted, runOps_halted] at hp
    exact hp.trans ha
  have hpNat : (runOps (controllerInput q full used) program (PA06A19PrepareRuntimeHeader019.natView before)).pc = 5 * (left.length + 24) := by
    rw [runOps_pc _ program _ program_noJump, program_length]
    change before.pc.toNat + 5 * 24 = _
    omega
  have hpcWord : (packingRun (controllerInput q full used) (left ++ program ++ right) 24 before).pc =
      BitVec.ofNat (indexWidth 32 full.length q) (5 * (left.length + 24)) := by
    have hp := congrArg (fun s : WordState (indexWidth 32 full.length q) => s.pc) he
    rw [word_pc, hpNat] at hp
    exact hp
  have hpcNat : (packingRun (controllerInput q full used) (left ++ program ++ right) 24 before).pc.toNat = 5 * (left.length + 24) := by
    rw [hpcWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((by
      simp only [List.length_append, program_length]
      omega : 5 * (left.length + 24) ≤ 5 * (left ++ program ++ right).length).trans_lt hpcCode)]
  have haddress : (packingRun (controllerInput q full used) (left ++ program ++ right) 24 before).register .address = before.register .address := by
    have hp := congrArg (fun s : WordState (indexWidth 32 full.length q) => s.register .address) he
    rw [word_register, program_address] at hp
    simpa only [PA06A19PrepareRuntimeHeader019.natView, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hp
  exact ⟨hhalt, hpcNat, haddress⟩

/-- Precisely the first six clauses of HeapRepresents for stage0/failedfalse.
This deliberately says nothing about metadata, initialUsed or table correctness. -/
def LiveFields (q : Nat) (full : List (Finset (Fin q))) (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q)) : Prop :=
  let bits := indexWidth 32 full.length q
  let t := treeSize q full
  let C := capacityWords 8192 full.length q t
  let P := packedCapacityWords q C bits
  (heap (BitVec.ofNat bits 0)).toNat = t ∧ (heap (BitVec.ofNat bits 1)).toNat = C ∧
  (heap (BitVec.ofNat bits 2)).toNat = P ∧ (heap (BitVec.ofNat bits 3)).toNat = bits ∧
  logicalHeap q C heap C = 0 ∧ logicalHeap q C heap (C + 1) = bit false

theorem logical_stage_failed {bits : Nat} (q C : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (hstage : heap (BitVec.ofNat bits (packedCapacityWords q C bits + 4)) = 0)
    (hfailed : heap (BitVec.ofNat bits (packedCapacityWords q C bits + 5)) = 0) :
    logicalHeap q C heap C = 0 ∧ logicalHeap q C heap (C + 1) = bit false := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have hnot : ¬ C + 1 < C := by omega
  have hd : C + 1 - C = 1 := by omega
  constructor
  · simp only [logicalHeap, hq0, ite_false, unpackHeap, Nat.lt_irrefl, ite_false,
      Nat.sub_self, Nat.add_zero, PA06A19PreparePackedView013.dataHeap_word]
    rw [Nat.add_comm 4 (packedCapacityWords q C bits), hstage]
    rfl
  · simp only [logicalHeap, hq0, ite_false, unpackHeap, hnot, hd, PA06A19PreparePackedView013.dataHeap_word]
    rw [show 4 + (packedCapacityWords q C bits + 1) = packedCapacityWords q C bits + 5 by omega, hfailed]
    rfl

theorem actual_liveFields (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hbank : BankData q full before) (hh : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ program ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ program ++ right).length)) :
    LiveFields q full (packingRun (controllerInput q full used) (left ++ program ++ right) 24 before).heap := by
  let bits := indexWidth 32 full.length q
  let t := treeSize q full
  let C := capacityWords 8192 full.length q t
  let P := packedCapacityWords q C bits
  let after := packingRun (controllerInput q full used) (left ++ program ++ right) 24 before
  let natural := PA06A19PrepareRuntimeHeader019.natView before
  have hat (n : Nat) (hn : Fits bits n) : after.heap (BitVec.ofNat bits n) =
      BitVec.ofNat bits (finalHeap t C P natural.heap n) := by
    have he := actual_heap q full used hq left right before hpc ha hbank hh hcode hpcCode (BitVec.ofNat bits n)
    change after.heap (BitVec.ofNat bits n) = BitVec.ofNat bits
      (finalHeap t C P natural.heap (BitVec.ofNat bits n).toNat) at he
    change n < 2 ^ bits at hn
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at he
    exact he
  have hv := finalHeap_values t C P natural.heap
  have hsmall : Fits bits 3 := (by decide : 3 ≤ 8).trans_lt (PA17WordBounds023.small_word_fit full.length q)
  have hinput := PA17GeneratorStatic048.input_le_maxWord full.length q 0 hq (by omega)
  have htree := PA06A19PrepareControlBank017.treeSize_bound full
  have htFit : Fits bits t := by
    have hle : t ≤ full.length + q + 1 := by dsimp only [t]; omega
    exact (hle.trans hinput).trans_lt (PA17GeneratorStatic048.maxWord_fits bits)
  have hCFit := PA06A19PrepareRuntimeLayout026.actual_capacity_fits q full hq
  rw [PA06A19PrepareRuntimeLayout026.capacityExpr_eq _ _ _ hq] at hCFit
  change C < 2 ^ bits at hCFit
  have hPFit := PA06A19PrepareRuntimeLayout026.actual_packed_fits q full hq
  rw [PA06A19PrepareRuntimeLayout026.capacityExpr_eq _ _ _ hq] at hPFit
  change P < 2 ^ bits at hPFit
  have hbB := PA17GeneratorStatic048.bits_le_maxWord full.length q 0 hq (by omega)
  have hbitsFit := hbB.trans_lt (PA17GeneratorStatic048.maxWord_fits bits)
  have hP5Fit : Fits bits (P + 5) := by
    have hc := PA06A19PrepareRuntimeLayout026.actual_bank_field_fits q full hq 5 (by decide)
    have hle : P + 5 ≤ PA06A19PrepareControlBank017.controlBase full.length q t P + 5 := by
      unfold PA06A19PrepareControlBank017.controlBase
      omega
    exact hle.trans_lt hc
  have hstage : after.heap (BitVec.ofNat bits (P + 4)) = 0 := by
    rw [hat _ ((by omega : P + 4 ≤ P + 5).trans_lt hP5Fit), hv.2.2.2.2.1]
    rfl
  have hfailed : after.heap (BitVec.ofNat bits (P + 5)) = 0 := by
    rw [hat _ hP5Fit, hv.2.2.2.2.2]
    rfl
  have hlogical := logical_stage_failed q C after.heap hq hstage hfailed
  have hbits := (input_natView q full hq before hbank hh).2.2.2
  refine ⟨?_, ?_, ?_, ?_, hlogical.1, hlogical.2⟩
  · rw [hat 0 ((by decide : 0 ≤ 3).trans_lt hsmall), hv.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htFit]
  · rw [hat 1 ((by decide : 1 ≤ 3).trans_lt hsmall), hv.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hCFit]
  · rw [hat 2 ((by decide : 2 ≤ 3).trans_lt hsmall), hv.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hPFit]
  · rw [hat 3 hsmall, hv.2.2.2.1, hbits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbitsFit]

theorem actual_frame (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hbank : BankData q full before) (hh : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ program ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q) (5 * (left ++ program ++ right).length))
    (point : BitVec (indexWidth 32 full.length q))
    (hout : point.toNat ≠ 0 ∧ point.toNat ≠ 1 ∧ point.toNat ≠ 2 ∧
      point.toNat ≠ packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) + 4 ∧
      point.toNat ≠ packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) + 5) :
    (packingRun (controllerInput q full used) (left ++ program ++ right) 24 before).heap point = before.heap point := by
  rw [actual_heap q full used hq left right before hpc ha hbank hh hcode hpcCode point]
  unfold finalHeap
  simp only [Function.update_of_ne hout.2.2.2.2, Function.update_of_ne hout.2.2.2.1,
    Function.update_of_ne hout.2.2.1, Function.update_of_ne hout.2.1, Function.update_of_ne hout.1]
  simp only [PA06A19PrepareRuntimeHeader019.natView, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem actual_trace_bound (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q)) :
    (packingDynamicTrace (controllerInput q full used) (left ++ program ++ right) 24 before).length ≤ 288 :=
  packingDynamicTrace_length_le _ _ _ before

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFinalHeader033
