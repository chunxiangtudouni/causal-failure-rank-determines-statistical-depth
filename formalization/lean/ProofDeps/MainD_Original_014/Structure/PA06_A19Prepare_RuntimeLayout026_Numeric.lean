module

public import Structure.PA06_A19Prepare_RuntimeLayout026_Bounds
public import PaperProofs.Structure.PA17_UniformGenerator_035p
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate: independently bounded actual prefixes of the six fixed
layout blocks. The final theorem discharges the numeric premises from the
original common-F8192 allocation and the temporary header's internal data. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety RawTreePreprocessingClaims CompactControllerClaims
  PA17UniformGenerator035j PA17UniformGenerator035m

theorem readInputs_numeric (rom : PhysicalROM) (B H : Nat) (hsmall : 10 ≤ B) (hH : 11 ≤ H)
    (hrom : 2 ≤ rom.input.length) (hN : rom.semantic.read .input 0 ≤ B)
    (hq : rom.semantic.read .input 1 ≤ B) (state : NatState) (hr : RegistersLE B state) :
    NumericSafe B H rom readInputs state := by
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 8 at hc
    interval_cases count <;> cases register <;>
      simp +decide [readInputs, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 8 at hc
    interval_cases count <;>
      simp +decide [readInputs, runOps, natExecuteOp, Op.execute, Instruction.execute,
        NatAccessFits, AccessFits, PhysicalROM.words]
    all_goals omega

theorem readTree_numeric (rom : PhysicalROM) (B H M t : Nat) (hsmall : 20 ≤ B)
    (hsourceB : 20 + 4 * M ≤ B) (hsourceH : 20 + 4 * M < H) (htB : t ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hM : state.heap 16 = M)
    (ht : state.heap (20 + 4 * M) = t) : NumericSafe B H rom readTree state := by
  have hM' : state.heap (M * 4 + 20) = t := by
    simpa only [Nat.mul_comm, Nat.add_comm] using ht
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 9 at hc
    interval_cases count <;> cases register <;>
      simp +decide [readTree, runOps, natExecuteOp, natArithmetic, Op.execute,
        Instruction.execute, hM, hM']
    all_goals omega
  · intro count hc
    change count < 9 at hc
    interval_cases count <;>
      simp +decide [readTree, runOps, natExecuteOp, natArithmetic, Op.execute,
        Instruction.execute, NatAccessFits, AccessFits, hM]
    all_goals omega

theorem computeCapacity_numeric (rom : PhysicalROM) (B H N q t : Nat)
    (hsmall : 8192 ≤ B) (hH : 13 ≤ H) (hC : capacityExpr N q t ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hN : state.heap 9 = N)
    (hq : state.register .total = q) (ht : state.register .value = t) :
    NumericSafe B H rom computeCapacity state := by
  have htable : (N + 1) * (q + 2) * (t + 1) ≤ B := by
    unfold capacityExpr at hC
    omega
  have hpair : (N + 1) * (q + 2) ≤ B :=
    (Nat.le_mul_of_pos_right _ (by omega)).trans htable
  have hN1 : N + 1 ≤ B := (Nat.le_mul_of_pos_right _ (by omega)).trans hpair
  have hq2 : q + 2 ≤ B := (Nat.le_mul_of_pos_left _ (by omega)).trans hpair
  have ht1 : t + 1 ≤ B :=
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))).trans htable
  unfold capacityExpr at hC
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 16 at hc
    interval_cases count <;> cases register <;>
      simp +decide [computeCapacity, runOps, natExecuteOp, natArithmetic, Op.execute,
        Instruction.execute, hN, hq, ht]
    all_goals omega
  · intro count hc
    change count < 16 at hc
    interval_cases count <;>
      simp +decide [computeCapacity, runOps, natExecuteOp, natArithmetic, Op.execute,
        Instruction.execute, NatAccessFits, AccessFits]
    all_goals omega

theorem computePacked_numeric (rom : PhysicalROM) (B H C width bits : Nat)
    (hsmall : 13 ≤ B) (hH : 14 ≤ H) (hwB : width ≤ B) (hbB : bits ≤ B)
    (hproduct : C * width + bits ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hC : state.register .value = C)
    (hw : state.heap 0 = width) (hb : state.heap 3 = bits) :
    NumericSafe B H rom computePacked state := by
  have hn : C * width + bits - 1 ≤ B := (Nat.sub_le _ _).trans hproduct
  have hp : (C * width + bits - 1) / bits ≤ B := (Nat.div_le_self _ _).trans hn
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 11 at hc
    interval_cases count <;> cases register <;>
      simp +decide [computePacked, runOps, natExecuteOp, natArithmetic, Op.execute,
        Instruction.execute, hC, hw, hb]
    all_goals omega
  · intro count hc
    change count < 11 at hc
    interval_cases count <;>
      simp +decide [computePacked, runOps, natExecuteOp, natArithmetic, Op.execute,
        Instruction.execute, NatAccessFits, AccessFits]
    all_goals omega

theorem computeDimensions_numeric (rom : PhysicalROM) (B H N q t : Nat)
    (hsmall : 14 ≤ B) (hH : 15 ≤ H) (hD : dimensionsExpr N q t ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hN : state.heap 9 = N)
    (hq : state.heap 10 = q) (ht : state.heap 11 = t) :
    NumericSafe B H rom computeDimensions state := by
  unfold dimensionsExpr at hD
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 12 at hc
    interval_cases count <;> cases register <;>
      simp +decide [computeDimensions, runOps, natExecuteOp, Op.execute, Instruction.execute,
        hN, hq, ht]
    all_goals omega
  · intro count hc
    change count < 12 at hc
    interval_cases count <;>
      simp +decide [computeDimensions, runOps, natExecuteOp, Op.execute, Instruction.execute,
        NatAccessFits, AccessFits]
    all_goals omega

theorem computeControl_numeric (rom : PhysicalROM) (B H P D : Nat)
    (hsmall : 4096 ≤ B) (hH : 16 ≤ H) (hCB : controlExpr P D ≤ B)
    (state : NatState) (hr : RegistersLE B state)
    (hP : state.register .value = P) (hD : state.register .total = D) :
    NumericSafe B H rom computeControl state := by
  unfold controlExpr at hCB
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 9 at hc
    interval_cases count <;> cases register <;>
      simp +decide [computeControl, runOps, natExecuteOp, natArithmetic, Op.execute,
        Instruction.execute, hP, hD]
    all_goals omega
  · intro count hc
    change count < 9 at hc
    interval_cases count <;>
      simp +decide [computeControl, runOps, natExecuteOp, natArithmetic, Op.execute,
        Instruction.execute, NatAccessFits, AccessFits]
    all_goals omega

/-- The finite short-block numeric interface. All bounds below concern
actual data and arithmetic, and are eliminated by actual_layout_numeric. -/
theorem layout_numeric (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (B H M t width bits : Nat) (hsmall : 8192 ≤ B) (hH : 16 ≤ H)
    (hN : full.length ≤ B) (hq : q ≤ B)
    (hsourceB : 20 + 4 * M ≤ B) (hsourceH : 20 + 4 * M < H)
    (htB : t ≤ B) (hwB : width ≤ B) (hbB : bits ≤ B)
    (hC : capacityExpr full.length q t ≤ B)
    (hproduct : capacityExpr full.length q t * width + bits ≤ B)
    (hD : dimensionsExpr full.length q t ≤ B)
    (hCB : controlExpr (packedExpr (capacityExpr full.length q t) width bits)
      (dimensionsExpr full.length q t) ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hM : state.heap 16 = M)
    (ht : state.heap (20 + 4 * M) = t) (hw : state.heap 0 = width) (hb : state.heap 3 = bits) :
    NumericSafe B H (controllerInput q full used) layout state := by
  let rom := controllerInput q full used
  let a := runOps rom readInputs state
  let b := runOps rom readTree a
  let c := runOps rom computeCapacity b
  let d := runOps rom computePacked c
  let e := runOps rom computeDimensions d
  have haH : a.heap = Function.update (Function.update state.heap 9 full.length) 10 q :=
    (readInputs_data rom state).1
  have haQ : a.register .total = q := (readInputs_data rom state).2
  have hfar9 : 20 + 4 * M ≠ 9 := by omega
  have hfar10 : 20 + 4 * M ≠ 10 := by omega
  have haM : a.heap 16 = M := by rw [haH]; simpa using hM
  have haT : a.heap (20 + 4 * M) = t := by
    rw [haH]
    simpa only [Function.update_of_ne hfar10, Function.update_of_ne hfar9] using ht
  have hbH : b.heap = Function.update a.heap 11 t := by
    have hh := (readTree_data rom a).1
    simpa only [haM, haT] using hh
  have hbT : b.register .value = t := by
    have hh := (readTree_data rom a).2.1
    simpa only [haM, haT] using hh
  have hbQ : b.register .total = q := (readTree_data rom a).2.2.trans haQ
  have hbN : b.heap 9 = full.length := by rw [hbH, haH]; simp
  have hcH : c.heap = Function.update b.heap 12 (capacityExpr full.length q t) := by
    simpa only [hbN, hbQ, hbT] using (computeCapacity_data rom b).1
  have hcC : c.register .value = capacityExpr full.length q t := by
    simpa only [hbN, hbQ, hbT] using (computeCapacity_data rom b).2
  have hcW : c.heap 0 = width := by rw [hcH, hbH, haH]; simpa using hw
  have hcBits : c.heap 3 = bits := by rw [hcH, hbH, haH]; simpa using hb
  have hdH : d.heap = Function.update c.heap 13
      (packedExpr (capacityExpr full.length q t) width bits) := by
    simpa only [hcC, hcW, hcBits] using (computePacked_data rom c).1
  have hdP : d.register .value = packedExpr (capacityExpr full.length q t) width bits := by
    simpa only [hcC, hcW, hcBits] using (computePacked_data rom c).2
  have hdN : d.heap 9 = full.length := by rw [hdH, hcH, hbH, haH]; simp
  have hdQ : d.heap 10 = q := by rw [hdH, hcH, hbH, haH]; simp
  have hdT : d.heap 11 = t := by rw [hdH, hcH, hbH]; simp
  have heD : e.register .total = dimensionsExpr full.length q t := by
    simpa only [hdN, hdQ, hdT] using (computeDimensions_data rom d).2.1
  have heP : e.register .value = packedExpr (capacityExpr full.length q t) width bits :=
    (computeDimensions_data rom d).2.2.trans hdP
  have hs1 := readInputs_numeric rom B H (by omega) (by omega)
    (by
      change 2 ≤ (controllerInput q full used).input.length
      simp only [controllerInput, rawIncidenceROM, List.length_append, List.length_cons, List.length_nil]
      omega) hN hq state hr
  have hs2 := readTree_numeric rom B H M t (by omega) hsourceB hsourceH htB a
    (hs1.final _ _ _ _ _) haM haT
  have hs3 := computeCapacity_numeric rom B H full.length q t hsmall (by omega) hC b
    (hs2.final _ _ _ _ _) hbN hbQ hbT
  have hs4 := computePacked_numeric rom B H (capacityExpr full.length q t) width bits
    (by omega) (by omega) hwB hbB hproduct c (hs3.final _ _ _ _ _) hcC hcW hcBits
  have hs5 := computeDimensions_numeric rom B H full.length q t (by omega) (by omega)
    hD d (hs4.final _ _ _ _ _) hdN hdQ hdT
  have hs6 := computeControl_numeric rom B H
    (packedExpr (capacityExpr full.length q t) width bits) (dimensionsExpr full.length q t)
    (by omega) hH hCB e (hs5.final _ _ _ _ _) heP heD
  have h12 := NumericSafe.append B H rom readInputs readTree state hs1 hs2
  have h123 := NumericSafe.append B H rom (readInputs ++ readTree) computeCapacity state h12 (by
    simpa only [runOps_append, a, b] using hs3)
  have h1234 := NumericSafe.append B H rom (readInputs ++ readTree ++ computeCapacity) computePacked state h123 (by
    simpa only [runOps_append, a, b, c] using hs4)
  have h12345 := NumericSafe.append B H rom (readInputs ++ readTree ++ computeCapacity ++ computePacked)
    computeDimensions state h1234 (by simpa only [runOps_append, a, b, c, d] using hs5)
  exact NumericSafe.append B H rom _ computeControl state h12345 (by
    simpa only [runOps_append, a, b, c, d, e] using hs6)

theorem maxWord_8192 (N q : Nat) (hq : 0 < q) : 8192 ≤ 2 ^ indexWidth 32 N q - 1 := by
  have hb := PA17GeneratorStatic048.bits_ge_64 N q hq
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  have hs : 8192 < 2 ^ 64 := by decide
  omega

theorem packedExpr_eq (N q t : Nat) (hq : 0 < q) :
    packedExpr (capacityExpr N q t) (CapacityBits.width q) (indexWidth 32 N q) =
      packedCapacityWords q (capacityWords 8192 N q t) (indexWidth 32 N q) := by
  rw [capacityExpr_eq N q t hq]
  rfl

/-- Actual-data numeric safety: no incoming safety predicate, small-word
side condition, or new allocation is required. RegistersLE is the canonical
Word view obligation, discharged in the Word theorem. -/
theorem actual_layout_numeric (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : NatState)
    (hr : RegistersLE (2 ^ indexWidth 32 full.length q - 1) state)
    (hM : state.heap 16 = full.length + q + 1)
    (ht : state.heap (20 + 4 * (full.length + q + 1)) = treeSize q full)
    (hw : state.heap 0 = CapacityBits.width q) (hb : state.heap 3 = indexWidth 32 full.length q) :
    NumericSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) layout state := by
  let bits := indexWidth 32 full.length q
  let B := 2 ^ bits - 1
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
  let H := PA06A19PrepareRuntimeHeader019.heapWords full.length q t
  have hAllocation : H = PA06A19PrepareControlBank017.allocation full.length q t P := by
    dsimp only [H, P, bits, PA06A19PrepareRuntimeHeader019.heapWords,
      PA06A19PrepareControlBank017.allocation, PA06A19PrepareControlBank017.dimensions,
      PA06A19PrepareControlBank017.mass]
    omega
  have hinput := PA17GeneratorStatic048.input_le_maxWord full.length q t hq (by
    have hh := PA06A19PrepareControlBank017.treeSize_bound full
    dsimp only [t]
    omega)
  have hbits := PA17GeneratorStatic048.bits_le_maxWord full.length q t hq (by
    have hh := PA06A19PrepareControlBank017.treeSize_bound full
    dsimp only [t]
    omega)
  have htree := PA06A19PrepareControlBank017.treeSize_bound full
  have hsmall := maxWord_8192 full.length q hq
  have hsource := actual_tree_source_fits q full hq
  have hsourceH : 20 + 4 * (full.length + q + 1) < H := by
    have hh := PA06A19PrepareControlBank017.source_target_disjoint full.length q t P hq
    have hh' : PA06A19PrepareControlBank017.cacheBase full.length q t P +
        PA06A19PrepareControlBank017.cacheAllowance full.length q < H := by
      rw [hAllocation]
      exact (PA06A19PrepareControlBank017.actual_cache_room full hq).1
    unfold PA06A19PrepareControlBank017.cacheLength PA06A19PrepareControlBank017.mass at hh
    omega
  have hC := actual_capacity_fits q full hq
  have hproduct := actual_product_plus_bits_fits q full hq
  have hCB := actual_bank_field_fits q full hq 0 (by decide)
  have hCB' : controlExpr (packedExpr (capacityExpr full.length q t)
      (CapacityBits.width q) bits) (dimensionsExpr full.length q t) < 2 ^ bits := by
    dsimp only [t, bits]
    rw [packedExpr_eq full.length q (treeSize q full) hq, controlExpr_eq]
    simpa only [Nat.add_zero, AlgorithmClaims.Fits] using hCB
  have hD : dimensionsExpr full.length q t ≤ B := by
    unfold controlExpr at hCB'
    dsimp only [B]
    omega
  apply layout_numeric q full used B H (full.length + q + 1) t (CapacityBits.width q) bits
    hsmall (by exact (by decide : 16 ≤ 69).trans (PA06A19PrepareRuntimeHeader019.heapWords_room _ _ _))
    (by dsimp only [B, bits]; omega) (by dsimp only [B, bits]; omega)
    (by change 20 + 4 * (full.length + q + 1) < 2 ^ bits at hsource; dsimp only [B]; omega)
    hsourceH (by dsimp only [B, bits, t]; omega)
    ((PA17PackingBounds043.width_le_bits full.length q).trans hbits) hbits
    (by change capacityExpr full.length q t < 2 ^ bits at hC; dsimp only [B]; omega)
    (by change capacityExpr full.length q t * CapacityBits.width q + bits < 2 ^ bits at hproduct
        dsimp only [B]; omega)
    hD (by dsimp only [B]; omega) state hr hM ht hw hb

theorem layout_noJump : ∀ op ∈ layout, NoJump op := by
  simp [layout, readInputs, readTree, computeCapacity, computePacked, computeDimensions, computeControl, NoJump]

theorem layout_safe (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hr : RegistersLE (2 ^ indexWidth 32 full.length q - 1) state)
    (hM : state.heap 16 = full.length + q + 1)
    (ht : state.heap (20 + 4 * (full.length + q + 1)) = treeSize q full)
    (hw : state.heap 0 = CapacityBits.width q) (hb : state.heap 3 = indexWidth 32 full.length q) :
    RunSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) (left ++ layout ++ right) 65 state := by
  exact straight_segment_safe _ _ _ left layout right layout_noJump state hpc ha
    (actual_layout_numeric q full used hq state hr hM ht hw hb)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026
