module

public import Structure.PA06_A19Prepare_RuntimeLayout026_Bounds
public import Structure.PA06_A19Prepare_FiniteClear025_Safety
public import PaperProofs.Structure.PA17_UniformGenerator_035p

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteClear031Setup

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety RawTreePreprocessingClaims CompactControllerClaims
  PA17UniformGenerator035j PA17UniformGenerator035m

/-- Actual finite ordinary domain of the old builder, including seven spills. -/
def ordinaryWords (N q t : Nat) : Nat := 6 * t + N + 2 * q + 31

/-- All dimensions are loaded from the permanent bank. Only 1/2/4/5/6/31
are scalar constants. The caller does not supply the clear length in a register. -/
def setup : List PackingOp :=
  [.base (.base (.constant .fresh 5)),
   .base (.base (.add .fresh .address .fresh)),
   .base (.base (.loadHeap .total .fresh)),
   .base (.base (.constant .fresh 2)),
   .base (.base (.add .fresh .address .fresh)),
   .base (.base (.loadHeap .value .fresh)),
   .base (.base (.constant .fresh 6)),
   .arithmetic .multiply .value .value .fresh,
   .base (.base (.add .total .total .value)),
   .base (.base (.loadHeap .value .address)),
   .base (.base (.add .total .total .value)),
   .base (.base (.constant .fresh 1)),
   .base (.base (.add .fresh .address .fresh)),
   .base (.base (.loadHeap .value .fresh)),
   .base (.base (.add .total .total .value)),
   .base (.base (.add .total .total .value)),
   .base (.base (.constant .value 31)),
   .base (.base (.add .total .total .value)),
   .base (.base (.constant .index 4))]

theorem setup_length : setup.length = 19 := rfl

theorem setup_noJump : ∀ op ∈ setup, NoJump op := by
  simp [setup, NoJump]

theorem setup_data (rom : PhysicalROM) (state : NatState) (CB N q t P : Nat)
    (hcb : state.register .address = CB)
    (hN : state.heap CB = N) (hq : state.heap (CB + 1) = q)
    (ht : state.heap (CB + 2) = t) (hP : state.heap (CB + 5) = P) :
    (runOps rom setup state).register .index = 4 ∧
      (runOps rom setup state).register .total = P + ordinaryWords N q t ∧
      (runOps rom setup state).register .address = CB ∧
      (runOps rom setup state).heap = state.heap := by
  simp +decide [setup, runOps, natExecuteOp, natArithmetic, Op.execute,
    Instruction.execute, hcb, hN, hq, ht, hP, ordinaryWords]
  omega

theorem setup_numeric (rom : PhysicalROM) (B H CB N q t P : Nat)
    (hsmall : 31 ≤ B) (hcbB : CB + 5 ≤ B) (hcbH : CB + 5 < H)
    (hcount : P + ordinaryWords N q t ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hcb : state.register .address = CB)
    (hN : state.heap CB = N) (hq : state.heap (CB + 1) = q)
    (ht : state.heap (CB + 2) = t) (hP : state.heap (CB + 5) = P) :
    NumericSafe B H rom setup state := by
  unfold ordinaryWords at hcount
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 19 at hc
    interval_cases count <;> cases register <;>
      simp +decide [setup, runOps, natExecuteOp, natArithmetic, Op.execute,
        Instruction.execute, hcb, hN, hq, ht, hP]
    all_goals omega
  · intro count hc
    change count < 19 at hc
    interval_cases count <;>
      simp +decide [setup, runOps, natExecuteOp, natArithmetic, Op.execute,
        Instruction.execute, NatAccessFits, AccessFits, hcb]
    all_goals omega

/-- The single cleared interval ends before the permanent bank. Thus it also
preserves every cached raw word and every bank field. -/
theorem clear_end_le_control (N q t P : Nat) :
    4 + (P + ordinaryWords N q t) ≤ PA06A19PrepareControlBank017.controlBase N q t P := by
  unfold ordinaryWords PA06A19PrepareControlBank017.controlBase PA06A19PrepareControlBank017.dimensions PA06A19PrepareControlBank017.mass
  omega

theorem actual_clear_end_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    let t := treeSize q full
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
    Fits (indexWidth 32 full.length q) (4 + (P + ordinaryWords full.length q t)) := by
  dsimp only
  exact (clear_end_le_control full.length q (treeSize q full) _).trans_lt
    (by simpa only [AlgorithmClaims.Fits, Nat.add_zero] using PA06A19PrepareRuntimeLayout026.actual_bank_field_fits q full hq 0 (by decide))


/-- All setup arithmetic and accesses fit the unchanged original allocation.
The bank equations are exactly the preceding real bank writer's outputs. -/
theorem actual_setup_numeric (q : Nat) (full : List (Finset (Fin q)))
    (used : Finset (Fin q)) (hq : 0 < q) (state : NatState)
    (hr : RegistersLE (2 ^ indexWidth 32 full.length q - 1) state)
    (hcb : state.register .address = PA06A19PrepareControlBank017.controlBase full.length q
      (treeSize q full) (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full))
        (indexWidth 32 full.length q)))
    (hN : state.heap (state.register .address) = full.length)
    (hQ : state.heap (state.register .address + 1) = q)
    (ht : state.heap (state.register .address + 2) = treeSize q full)
    (hP : state.heap (state.register .address + 5) =
      packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full))
        (indexWidth 32 full.length q)) :
    NumericSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) setup state := by
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) (indexWidth 32 full.length q)
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  let B := 2 ^ indexWidth 32 full.length q - 1
  let H := PA06A19PrepareRuntimeHeader019.heapWords full.length q t
  have cb : state.register .address = CB := hcb
  have hCBfit := PA06A19PrepareRuntimeLayout026.actual_bank_field_fits q full hq 5 (by decide)
  have hendfit := actual_clear_end_fits q full hq
  have hsource := PA06A19PrepareControlBank017.controls_cache_disjoint
    full.length q t P 5 (by decide)
  have hcache : PA06A19PrepareControlBank017.cacheBase full.length q t P +
      PA06A19PrepareControlBank017.cacheAllowance full.length q <
      PA06A19PrepareControlBank017.allocation full.length q t P :=
    (PA06A19PrepareControlBank017.actual_cache_room full hq).1
  have hAlloc : PA06A19PrepareControlBank017.allocation full.length q t P = H := by
    dsimp only [H, P, t, PA06A19PrepareControlBank017.allocation,
      PA06A19PrepareRuntimeHeader019.heapWords, PA06A19PrepareControlBank017.dimensions,
      PA06A19PrepareControlBank017.mass]
    omega
  have hCBH : CB + 5 < H := by
    have hc : PA06A19PrepareControlBank017.cacheBase full.length q t P < H := by
      rw [hAlloc] at hcache
      exact (Nat.le_add_right _ _).trans_lt hcache
    exact hsource.trans hc
  apply setup_numeric (controllerInput q full used) B H CB full.length q t P
  · have hh : 31 ≤ capacityWords 8192 full.length q t := by
      unfold capacityWords
      rw [ite_eq_right (Nat.ne_of_gt hq)]
      omega
    have hf := PA06A19PrepareRuntimeLayout026.actual_capacity_fits q full hq
    rw [PA06A19PrepareRuntimeLayout026.capacityExpr_eq _ _ _ hq] at hf
    change capacityWords 8192 full.length q t < 2 ^ indexWidth 32 full.length q at hf
    dsimp only [B]
    omega
  · change CB + 5 < 2 ^ indexWidth 32 full.length q at hCBfit
    dsimp only [B]
    omega
  · exact hCBH
  · change 4 + (P + ordinaryWords full.length q t) < 2 ^ indexWidth 32 full.length q at hendfit
    dsimp only [B]
    omega
  · exact hr
  · exact cb
  · simpa only [cb] using hN
  · simpa only [cb] using hQ
  · simpa only [cb] using ht
  · simpa only [cb] using hP

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteClear031Setup
