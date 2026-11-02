module

public import Structure.PA06_A19Prepare_RuntimeLayout026
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Uncompiled candidate: real relative stores of the agreed permanent
bank fields 0=N,1=q,2=t,3=C0,4=Cnew,5=P,6=4+P. The low layout results are
read by actual instructions; hardware.address is preserved as CB. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM

def oldCapacityExpr (N q t : Nat) : Nat := tableWords N q t + 2 * (t + 1)

def lowToBank (source offset : Nat) : List PackingOp :=
  [.base (.base (.constant .index source)), .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .index offset)), .base (.base (.add .index .address .index)),
   .base (.base (.storeHeap .index .total))]

/-- Actual C0 calculation uses Cnew-q-8190*(t+1), with all subtraction
arguments nonnegative at the proved layout values. -/
def writeOldCapacity : List PackingOp :=
  [.base (.base (.constant .index 12)), .base (.base (.loadHeap .value .index)),
   .base (.base (.constant .index 10)), .base (.base (.loadHeap .total .index)),
   .base (.subtract .value .value .total), .base (.base (.constant .index 11)),
   .base (.base (.loadHeap .total .index)), .base (.base (.constant .old 1)),
   .base (.base (.add .total .total .old)), .base (.base (.constant .old 8190)),
   .arithmetic .multiply .total .total .old, .base (.subtract .value .value .total),
   .base (.base (.constant .index 3)), .base (.base (.add .index .address .index)),
   .base (.base (.storeHeap .index .value))]

def writeIndexBase : List PackingOp :=
  [.base (.base (.constant .index 13)), .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .old 4)), .base (.base (.add .total .total .old)),
   .base (.base (.constant .index 6)), .base (.base (.add .index .address .index)),
   .base (.base (.storeHeap .index .total))]

def bankSetup : List PackingOp := lowToBank 9 0 ++ lowToBank 10 1 ++ lowToBank 11 2 ++ writeOldCapacity ++
  lowToBank 12 4 ++ lowToBank 13 5 ++ writeIndexBase

theorem bankSetup_length : bankSetup.length = 47 := rfl

theorem oldCapacity_difference (N q t : Nat) :
    (capacityExpr N q t - q) - (t + 1) * 8190 = oldCapacityExpr N q t := by
  unfold capacityExpr oldCapacityExpr tableWords cells
  omega

theorem lowToBank_heap (source offset : Nat) (rom : PhysicalROM) (state : NatState) :
    (runOps rom (lowToBank source offset) state).heap =
      Function.update state.heap (state.register .address + offset) (state.heap source) := rfl

theorem lowToBank_address (source offset : Nat) (rom : PhysicalROM) (state : NatState) :
    (runOps rom (lowToBank source offset) state).register .address = state.register .address := rfl

theorem writeOldCapacity_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom writeOldCapacity state).heap = Function.update state.heap (state.register .address + 3)
      ((state.heap 12 - state.heap 10) - (state.heap 11 + 1) * 8190) := by
  simp +decide only [writeOldCapacity, runOps, natExecuteOp, natArithmetic, Op.execute,
    Instruction.execute, Function.update_apply, ↓reduceIte]

theorem writeOldCapacity_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom writeOldCapacity state).register .address = state.register .address := rfl

theorem writeIndexBase_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom writeIndexBase state).heap = Function.update state.heap (state.register .address + 6) (state.heap 13 + 4) := by
  simp +decide only [writeIndexBase, runOps, natExecuteOp, Op.execute,
    Instruction.execute, Function.update_apply, ↓reduceIte]

theorem writeIndexBase_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom writeIndexBase state).register .address = state.register .address := rfl

def bankFields (N q t P CB : Nat) (heap : Nat → Nat) : Nat → Nat :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update heap (CB + 0) N) (CB + 1) q) (CB + 2) t) (CB + 3) (oldCapacityExpr N q t))
    (CB + 4) (capacityExpr N q t)) (CB + 5) P) (CB + 6) (P + 4)

theorem bankSetup_heap (rom : PhysicalROM) (state : NatState) (N q t P : Nat)
    (hCB : 16 ≤ state.register .address)
    (hN : state.heap 9 = N) (hq : state.heap 10 = q) (ht : state.heap 11 = t)
    (hC : state.heap 12 = capacityExpr N q t) (hP : state.heap 13 = P) :
    (runOps rom bankSetup state).heap = bankFields N q t P (state.register .address) state.heap := by
  have hne10 (offset : Nat) : 10 ≠ state.register .address + offset := by omega
  have hne11 (offset : Nat) : 11 ≠ state.register .address + offset := by omega
  have hne12 (offset : Nat) : 12 ≠ state.register .address + offset := by omega
  have hne13 (offset : Nat) : 13 ≠ state.register .address + offset := by omega
  simp only [bankSetup, runOps_append, writeIndexBase_heap, lowToBank_heap, lowToBank_address,
    writeOldCapacity_heap, writeOldCapacity_address]
  simp only [bankFields, Function.update_apply, hne10, hne11, hne12, hne13, ite_false,
    hN, hq, ht, hC, hP, oldCapacity_difference]

theorem bankSetup_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom bankSetup state).register .address = state.register .address := by
  simp only [bankSetup, runOps_append, lowToBank_address, writeOldCapacity_address, writeIndexBase_address]

theorem bankSetup_frame (rom : PhysicalROM) (state : NatState) (N q t P : Nat)
    (hCB : 16 ≤ state.register .address)
    (hN : state.heap 9 = N) (hq : state.heap 10 = q) (ht : state.heap 11 = t)
    (hC : state.heap 12 = capacityExpr N q t) (hP : state.heap 13 = P)
    (address : Nat) (ha : address < state.register .address ∨ state.register .address + 7 ≤ address) :
    (runOps rom bankSetup state).heap address = state.heap address := by
  rw [bankSetup_heap rom state N q t P hCB hN hq ht hC hP]
  unfold bankFields
  simp only [Function.update_of_ne (show address ≠ state.register .address + 0 by omega),
    Function.update_of_ne (show address ≠ state.register .address + 1 by omega),
    Function.update_of_ne (show address ≠ state.register .address + 2 by omega),
    Function.update_of_ne (show address ≠ state.register .address + 3 by omega),
    Function.update_of_ne (show address ≠ state.register .address + 4 by omega),
    Function.update_of_ne (show address ≠ state.register .address + 5 by omega),
    Function.update_of_ne (show address ≠ state.register .address + 6 by omega)]

theorem bankSetup_fields (rom : PhysicalROM) (state : NatState) (N q t P : Nat)
    (hCB : 16 ≤ state.register .address)
    (hN : state.heap 9 = N) (hq : state.heap 10 = q) (ht : state.heap 11 = t)
    (hC : state.heap 12 = capacityExpr N q t) (hP : state.heap 13 = P) :
    let fresh := runOps rom bankSetup state
    fresh.heap (state.register .address + 0) = N ∧ fresh.heap (state.register .address + 1) = q ∧
    fresh.heap (state.register .address + 2) = t ∧ fresh.heap (state.register .address + 3) = oldCapacityExpr N q t ∧
    fresh.heap (state.register .address + 4) = capacityExpr N q t ∧ fresh.heap (state.register .address + 5) = P ∧
    fresh.heap (state.register .address + 6) = 4 + P := by
  simp only [bankSetup_heap rom state N q t P hCB hN hq ht hC hP]
  simp +decide [bankFields]
  omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026
