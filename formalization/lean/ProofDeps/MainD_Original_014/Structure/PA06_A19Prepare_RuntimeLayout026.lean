module

public import Structure.PA06_A19Prepare_RuntimeHeader019
public import Structure.PA06_A19Prepare_ControlBank017_Geometry
public import PaperProofs.Structure.PA17_PackingBounds_043
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Uncompiled candidate: fixed actual runtime layout calculation. Original
ROM[0]/ROM[1] supply N/q; actual raw cache heap16 and heap(20+4*M) supply
M/t. Header width/bits are internal outputs of the preceding real 024.
No data dimension, capacity, packed size or control base is a code literal.
This first file proves Nat execution/data/frame; Word safety is separate. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  CompactControllerClaims

def capacityExpr (N q t : Nat) : Nat := (N + 1) * (q + 2) * (t + 1) + q + 8192 * (t + 1)
def packedExpr (C width bits : Nat) : Nat := (C * width + bits - 1) / bits
def dimensionsExpr (N q t : Nat) : Nat := N + q + t + 1
def controlExpr (P D : Nat) : Nat := 4096 * D + P + 4

def readInputs : List PackingOp :=
  [.base (.base (.constant .index 0)), .base (.base (.loadROM .input .total .index)),
   .base (.base (.constant .index 9)), .base (.base (.storeHeap .index .total)),
   .base (.base (.constant .index 1)), .base (.base (.loadROM .input .total .index)),
   .base (.base (.constant .index 10)), .base (.base (.storeHeap .index .total))]

def readTree : List PackingOp :=
  [.base (.base (.constant .index 16)), .base (.base (.loadHeap .value .index)),
   .base (.base (.constant .old 4)), .arithmetic .multiply .index .value .old,
   .base (.base (.constant .old 20)), .base (.base (.add .index .index .old)),
   .base (.base (.loadHeap .value .index)), .base (.base (.constant .index 11)),
   .base (.base (.storeHeap .index .value))]

def computeCapacity : List PackingOp :=
  [.base (.base (.constant .fresh 1)), .base (.base (.add .fresh .value .fresh)),
   .base (.base (.constant .index 9)), .base (.base (.loadHeap .old .index)),
   .base (.base (.constant .index 1)), .base (.base (.add .old .old .index)),
   .base (.base (.constant .index 2)), .base (.base (.add .value .total .index)),
   .arithmetic .multiply .value .old .value, .arithmetic .multiply .value .value .fresh,
   .base (.base (.add .value .value .total)), .base (.base (.constant .old 8192)),
   .arithmetic .multiply .old .old .fresh, .base (.base (.add .value .value .old)),
   .base (.base (.constant .index 12)), .base (.base (.storeHeap .index .value))]

def computePacked : List PackingOp :=
  [.base (.base (.constant .index 0)), .base (.base (.loadHeap .total .index)),
   .arithmetic .multiply .value .value .total,
   .base (.base (.constant .index 3)), .base (.base (.loadHeap .total .index)),
   .base (.base (.add .value .value .total)), .base (.base (.constant .old 1)),
   .base (.subtract .value .value .old), .arithmetic .divide .value .value .total,
   .base (.base (.constant .index 13)), .base (.base (.storeHeap .index .value))]

def computeDimensions : List PackingOp :=
  [.base (.base (.constant .index 9)), .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .index 10)), .base (.base (.loadHeap .old .index)),
   .base (.base (.add .total .total .old)), .base (.base (.constant .index 11)),
   .base (.base (.loadHeap .old .index)), .base (.base (.add .total .total .old)),
   .base (.base (.constant .old 1)), .base (.base (.add .total .total .old)),
   .base (.base (.constant .index 14)), .base (.base (.storeHeap .index .total))]

def computeControl : List PackingOp :=
  [.base (.base (.constant .old 4096)), .arithmetic .multiply .total .old .total,
   .base (.base (.add .total .total .value)), .base (.base (.constant .old 4)),
   .base (.base (.add .total .total .old)), .base (.base (.constant .index 15)),
   .base (.base (.storeHeap .index .total)), .base (.base (.constant .address 15)),
   .base (.base (.loadHeap .address .address))]

def layout : List PackingOp := readInputs ++ readTree ++ computeCapacity ++ computePacked ++ computeDimensions ++ computeControl

theorem layout_length : layout.length = 65 := rfl

theorem readInputs_data (rom : PhysicalROM) (state : NatState) :
    (runOps rom readInputs state).heap = Function.update
      (Function.update state.heap 9 (rom.semantic.read .input 0)) 10 (rom.semantic.read .input 1) ∧
    (runOps rom readInputs state).register .total = rom.semantic.read .input 1 := by
  constructor <;> simp +decide only [readInputs, runOps, natExecuteOp, Op.execute, Instruction.execute,
    Function.update_apply, ↓reduceIte]

theorem readTree_data (rom : PhysicalROM) (state : NatState) :
    (runOps rom readTree state).heap = Function.update state.heap 11 (state.heap (20 + 4 * state.heap 16)) ∧
    (runOps rom readTree state).register .value = state.heap (20 + 4 * state.heap 16) ∧
    (runOps rom readTree state).register .total = state.register .total := by
  constructor
  · simp +decide only [readTree, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
      Function.update_apply, ↓reduceIte, Nat.mul_comm, Nat.add_comm]
  · constructor
    · simp +decide only [readTree, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
        Function.update_apply, ↓reduceIte, Nat.mul_comm, Nat.add_comm]
    · rfl

theorem computeCapacity_data (rom : PhysicalROM) (state : NatState) :
    (runOps rom computeCapacity state).heap = Function.update state.heap 12
      (capacityExpr (state.heap 9) (state.register .total) (state.register .value)) ∧
    (runOps rom computeCapacity state).register .value = capacityExpr (state.heap 9) (state.register .total) (state.register .value) := by
  constructor <;> simp +decide only [computeCapacity, runOps, natExecuteOp, natArithmetic, Op.execute,
    Instruction.execute, Function.update_apply, ↓reduceIte, capacityExpr]

theorem computePacked_data (rom : PhysicalROM) (state : NatState) :
    (runOps rom computePacked state).heap = Function.update state.heap 13
      (packedExpr (state.register .value) (state.heap 0) (state.heap 3)) ∧
    (runOps rom computePacked state).register .value = packedExpr (state.register .value) (state.heap 0) (state.heap 3) := by
  constructor <;> simp +decide only [computePacked, runOps, natExecuteOp, natArithmetic, Op.execute,
    Instruction.execute, Function.update_apply, ↓reduceIte, packedExpr]

theorem computeDimensions_data (rom : PhysicalROM) (state : NatState) :
    (runOps rom computeDimensions state).heap = Function.update state.heap 14
      (dimensionsExpr (state.heap 9) (state.heap 10) (state.heap 11)) ∧
    (runOps rom computeDimensions state).register .total = dimensionsExpr (state.heap 9) (state.heap 10) (state.heap 11) ∧
    (runOps rom computeDimensions state).register .value = state.register .value := by
  constructor
  · simp +decide only [computeDimensions, runOps, natExecuteOp, Op.execute, Instruction.execute,
      Function.update_apply, ↓reduceIte, dimensionsExpr]
  · constructor
    · simp +decide only [computeDimensions, runOps, natExecuteOp, Op.execute, Instruction.execute,
        Function.update_apply, ↓reduceIte, dimensionsExpr]
    · rfl

theorem computeControl_data (rom : PhysicalROM) (state : NatState) :
    (runOps rom computeControl state).heap = Function.update state.heap 15
      (controlExpr (state.register .value) (state.register .total)) ∧
    (runOps rom computeControl state).register .address = controlExpr (state.register .value) (state.register .total) := by
  constructor <;> simp +decide only [computeControl, runOps, natExecuteOp, natArithmetic, Op.execute,
    Instruction.execute, Function.update_apply, ↓reduceIte, controlExpr]

private theorem readInputs_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom readInputs state).heap = Function.update (Function.update state.heap 9 (rom.semantic.read .input 0)) 10 (rom.semantic.read .input 1) :=
  (readInputs_data rom state).1

private theorem readInputs_total (rom : PhysicalROM) (state : NatState) :
    (runOps rom readInputs state).register .total = rom.semantic.read .input 1 :=
  (readInputs_data rom state).2

private theorem readTree_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom readTree state).heap = Function.update state.heap 11 (state.heap (20 + 4 * state.heap 16)) :=
  (readTree_data rom state).1

private theorem readTree_value (rom : PhysicalROM) (state : NatState) :
    (runOps rom readTree state).register .value = state.heap (20 + 4 * state.heap 16) :=
  (readTree_data rom state).2.1

private theorem readTree_total (rom : PhysicalROM) (state : NatState) :
    (runOps rom readTree state).register .total = state.register .total :=
  (readTree_data rom state).2.2

private theorem computeCapacity_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom computeCapacity state).heap = Function.update state.heap 12 (capacityExpr (state.heap 9) (state.register .total) (state.register .value)) :=
  (computeCapacity_data rom state).1

private theorem computeCapacity_value (rom : PhysicalROM) (state : NatState) :
    (runOps rom computeCapacity state).register .value = capacityExpr (state.heap 9) (state.register .total) (state.register .value) :=
  (computeCapacity_data rom state).2

private theorem computePacked_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom computePacked state).heap = Function.update state.heap 13 (packedExpr (state.register .value) (state.heap 0) (state.heap 3)) :=
  (computePacked_data rom state).1

private theorem computePacked_value (rom : PhysicalROM) (state : NatState) :
    (runOps rom computePacked state).register .value = packedExpr (state.register .value) (state.heap 0) (state.heap 3) :=
  (computePacked_data rom state).2

private theorem computeDimensions_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom computeDimensions state).heap = Function.update state.heap 14 (dimensionsExpr (state.heap 9) (state.heap 10) (state.heap 11)) :=
  (computeDimensions_data rom state).1

private theorem computeDimensions_total (rom : PhysicalROM) (state : NatState) :
    (runOps rom computeDimensions state).register .total = dimensionsExpr (state.heap 9) (state.heap 10) (state.heap 11) :=
  (computeDimensions_data rom state).2.1

private theorem computeDimensions_value (rom : PhysicalROM) (state : NatState) :
    (runOps rom computeDimensions state).register .value = state.register .value :=
  (computeDimensions_data rom state).2.2

private theorem computeControl_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom computeControl state).heap = Function.update state.heap 15 (controlExpr (state.register .value) (state.register .total)) :=
  (computeControl_data rom state).1

private theorem computeControl_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom computeControl state).register .address = controlExpr (state.register .value) (state.register .total) :=
  (computeControl_data rom state).2

def lowFields (N q t width bits : Nat) (heap : Nat → Nat) : Nat → Nat :=
  let C := capacityExpr N q t
  let P := packedExpr C width bits
  let D := dimensionsExpr N q t
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update heap 9 N) 10 q) 11 t) 12 C) 13 P) 14 D) 15 (controlExpr P D)

theorem layout_data (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (state : NatState) (M t width bits : Nat)
    (hM : state.heap 16 = M) (ht : state.heap (20 + 4 * M) = t)
    (hw : state.heap 0 = width) (hb : state.heap 3 = bits) :
    (runOps (controllerInput q full used) layout state).heap = lowFields full.length q t width bits state.heap ∧
    (runOps (controllerInput q full used) layout state).register .address =
      controlExpr (packedExpr (capacityExpr full.length q t) width bits) (dimensionsExpr full.length q t) := by
  have hn : (controllerInput q full used).semantic.read .input 0 = full.length := rfl
  have hq : (controllerInput q full used).semantic.read .input 1 = q := rfl
  have h9 : 20 + 4 * M ≠ 9 := by omega
  have h10 : 20 + 4 * M ≠ 10 := by omega
  constructor
  · simp only [layout, runOps_append, computeControl_heap, computeDimensions_heap, computeDimensions_total,
      computeDimensions_value, computePacked_heap, computePacked_value, computeCapacity_heap, computeCapacity_value,
      readTree_heap, readTree_value, readTree_total, readInputs_heap, readInputs_total]
    simp +decide only [lowFields, Function.update_apply, ↓reduceIte, hn, hq, hM, ht, hw, hb, h9, h10]
  · simp only [layout, runOps_append, computeControl_address, computeDimensions_total,
      computeDimensions_value, computePacked_heap, computePacked_value, computeCapacity_heap, computeCapacity_value,
      readTree_heap, readTree_value, readTree_total, readInputs_heap, readInputs_total]
    simp +decide only [Function.update_apply, ↓reduceIte, hn, hq, hM, ht, hw, hb, h9, h10]

theorem capacityExpr_eq (N q t : Nat) (hq : 0 < q) :
    capacityExpr N q t = capacityWords 8192 N q t := by
  unfold capacityExpr capacityWords tableWords cells
  rw [ite_eq_right (Nat.ne_of_gt hq)]

theorem controlExpr_eq (N q t P : Nat) :
    controlExpr P (dimensionsExpr N q t) = PA06A19PrepareControlBank017.controlBase N q t P := by
  unfold controlExpr dimensionsExpr PA06A19PrepareControlBank017.controlBase
    PA06A19PrepareControlBank017.dimensions PA06A19PrepareControlBank017.mass
  omega

theorem layout_frame (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (state : NatState) (M t width bits : Nat)
    (hM : state.heap 16 = M) (ht : state.heap (20 + 4 * M) = t)
    (hw : state.heap 0 = width) (hb : state.heap 3 = bits)
    (address : Nat) (ha : address < 9 ∨ 16 ≤ address) :
    (runOps (controllerInput q full used) layout state).heap address = state.heap address := by
  rw [(layout_data q full used state M t width bits hM ht hw hb).1]
  unfold lowFields
  simp only [Function.update_of_ne (show address ≠ 9 by omega), Function.update_of_ne (show address ≠ 10 by omega),
    Function.update_of_ne (show address ≠ 11 by omega), Function.update_of_ne (show address ≠ 12 by omega),
    Function.update_of_ne (show address ≠ 13 by omega), Function.update_of_ne (show address ≠ 14 by omega),
    Function.update_of_ne (show address ≠ 15 by omega)]

/-- These are the nine REAL setup operations required by the already-
proved 017 copy ABI; the destination is computed before address becomes 0. -/
def setupCopy : List PackingOp :=
  [.base (.base (.constant .index 512)), .base (.base (.add .index .address .index)),
   .base (.base (.constant .total 16)), .base (.base (.loadHeap .total .total)),
   .base (.base (.constant .fresh 5)), .arithmetic .multiply .total .total .fresh,
   .base (.base (.constant .fresh 21)), .base (.base (.add .total .total .fresh)),
   .base (.base (.constant .address 0))]

def restoreControl : List PackingOp :=
  [.base (.base (.constant .address 15)), .base (.base (.loadHeap .address .address))]

theorem setupCopy_length : setupCopy.length = 9 := rfl
theorem restoreControl_length : restoreControl.length = 2 := rfl

theorem setupCopy_data (rom : PhysicalROM) (state : NatState) :
    (runOps rom setupCopy state).register .address = 0 ∧
    (runOps rom setupCopy state).register .index = state.register .address + 512 ∧
    (runOps rom setupCopy state).register .total = 21 + 5 * state.heap 16 ∧
    (runOps rom setupCopy state).heap = state.heap := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · simp +decide only [setupCopy, runOps, natExecuteOp, natArithmetic, Op.execute,
          Instruction.execute, Function.update_apply, ↓reduceIte, Nat.mul_comm, Nat.add_comm]
      · rfl

theorem restoreControl_data (rom : PhysicalROM) (state : NatState) :
    (runOps rom restoreControl state).register .address = state.heap 15 ∧
    (runOps rom restoreControl state).heap = state.heap := ⟨rfl, rfl⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026
