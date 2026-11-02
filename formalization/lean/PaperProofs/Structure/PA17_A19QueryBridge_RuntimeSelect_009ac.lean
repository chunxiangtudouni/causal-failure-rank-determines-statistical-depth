module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009ab

/-! Fixed runtime descent assembly. It executes exactly t fuel-controlled
rounds, preserving an already found tool after node0. Reading leaf0 at node0
is masked, as in the original010b block; the canonical tree is nonempty.
Node/tool slots stay c+t+1/+2 and every actual store is strictly below E. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def nodeSlot (header q size : Nat) : Nat := childBase header q + size + 1
def toolSlot (header q size : Nat) : Nat := childBase header q + size + 2

def descendInit : List PackingOp :=
  [.base (.base (.constant .index 0)), .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .flag 1)), .base (.base (.add .fresh .total .flag)),
   .base (.base (.constant .index 10)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .old .index)), .base (.base (.add .old .old .fresh)),
   .base (.base (.constant .index 14)), .base (.base (.add .index .address .index)),
   .base (.base (.storeHeap .index .old)), .base (.base (.add .old .old .flag)),
   .base (.base (.constant .index 15)), .base (.base (.add .index .address .index)),
   .base (.base (.storeHeap .index .old)), .base (.base (.constant .index 13)),
   .base (.base (.add .index .address .index)), .base (.base (.storeHeap .index .total)),
   .base (.base (.constant .index 1)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .value .index)), .base (.subtract .old .old .flag),
   .base (.base (.storeHeap .old .value)), .base (.base (.constant .value 0)),
   .base (.base (.add .old .old .flag)), .base (.base (.storeHeap .old .value))]

def descendTestLead (origin : Nat) : List PackingOp :=
  [.base (.base (.constant .index 13)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .total .index)), .base (.base (.constant .old (5 * (origin + 91))))]

def descendTest (origin : Nat) : List PackingOp := descendTestLead origin ++ [.jumpIfZero .total .old]

def descendIndex : List PackingOp :=
  [.base (.base (.constant .index 14)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .index .index)), .base (.base (.loadHeap .fresh .index)),
   .base (.base (.constant .flag 1)), .base (.subtract .index .fresh .flag)]

def descendTailLead (origin : Nat) : List PackingOp :=
  [.base (.base (.constant .index 14)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .index .index)), .base (.base (.loadHeap .old .index)),
   .base (.base (.constant .index 15)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .index .index)), .base (.base (.loadHeap .fresh .index)),
   .base (.base (.constant .flag 0)), .base (.base (.select .flag .old .value .flag)),
   .base (.base (.select .value .flag .flag .fresh)), .base (.base (.storeHeap .index .value)),
   .base (.base (.constant .index 10)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .index .index)), .base (.base (.add .index .index .old)),
   .base (.base (.loadHeap .fresh .index)), .base (.base (.constant .total 0)),
   .base (.base (.select .fresh .flag .total .fresh)),
   .base (.base (.constant .index 14)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .index .index)), .base (.base (.storeHeap .index .fresh)),
   .base (.base (.constant .index 13)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .total .index)), .base (.base (.constant .flag 1)),
   .base (.subtract .total .total .flag), .base (.base (.storeHeap .index .total)),
   .base (.base (.constant .old (5 * origin))), .base (.base (.constant .flag 0))]

def descendTail (origin : Nat) : List PackingOp := descendTailLead origin ++ [.jumpIfZero .flag .old]
def descendBodyLead (origin : Nat) : List PackingOp := descendIndex ++ leafReadProgram ++ descendTailLead origin
def descendBody (origin : Nat) : List PackingOp := descendBodyLead origin ++ [.jumpIfZero .flag .old]
def descendProgramAt (origin : Nat) : List PackingOp := descendTest origin ++ descendBody origin

def selectionCoreAt (origin : Nat) : List PackingOp := parentProgramAt origin ++ descendInit ++ descendProgramAt (origin + 190)
def descendSteps (size : Nat) : Nat := 91 * size + 5

theorem descendInit_length : descendInit.length = 26 := rfl
theorem descendTestLead_length (origin : Nat) : (descendTestLead origin).length = 4 := rfl
theorem descendTest_length (origin : Nat) : (descendTest origin).length = 5 := rfl
theorem descendIndex_length : descendIndex.length = 6 := rfl
theorem descendTailLead_length (origin : Nat) : (descendTailLead origin).length = 31 := rfl
theorem descendTail_length (origin : Nat) : (descendTail origin).length = 32 := rfl
theorem descendBodyLead_length (origin : Nat) : (descendBodyLead origin).length = 85 := rfl
theorem descendBody_length (origin : Nat) : (descendBody origin).length = 86 := rfl
theorem descendProgramAt_length (origin : Nat) : (descendProgramAt origin).length = 91 := rfl
theorem selectionCoreAt_length (origin : Nat) : (selectionCoreAt origin).length = 281 := rfl

theorem descendInit_straight : StraightProgram descendInit := by simp [descendInit, StraightProgram, StraightOp]
theorem descendTestLead_straight (origin : Nat) : StraightProgram (descendTestLead origin) := by
  simp [descendTestLead, StraightProgram, StraightOp]
theorem descendIndex_straight : StraightProgram descendIndex := by simp [descendIndex, StraightProgram, StraightOp]
theorem descendTailLead_straight (origin : Nat) : StraightProgram (descendTailLead origin) := by
  simp [descendTailLead, StraightProgram, StraightOp]

theorem descendIndex_result {bits : Nat} (rom : PhysicalROM) (header pointer current : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hcurrent : Fits bits current) (hh : state.register .address = BitVec.ofNat bits header)
    (hptr : state.heap (BitVec.ofNat bits (header + 14)) = BitVec.ofNat bits pointer)
    (hnode : state.heap (BitVec.ofNat bits pointer) = BitVec.ofNat bits current) :
    let after := executeOps rom descendIndex state
    after.register .index = BitVec.ofNat bits (current - 1) ∧ after.register .address = BitVec.ofNat bits header ∧ after.heap = state.heap := by
  simp +decide [descendIndex, executeOps, packingExecuteOp, wordOp, wordInstruction, hh, hptr, hnode,
    BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hcurrent]

theorem descendTest_result {bits : Nat} (rom : PhysicalROM) (origin header remaining : Nat) (state : WordState bits)
    (hr : Fits bits remaining) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin))
    (hnode : state.heap (BitVec.ofNat bits (header + 13)) = BitVec.ofNat bits remaining) :
    let after := executeOps rom (descendTest origin) state
    after.pc = BitVec.ofNat bits (if remaining = 0 then 5 * (origin + 91) else 5 * (origin + 5)) ∧
      after.register .address = BitVec.ofNat bits header ∧ after.heap = state.heap := by
  simp +decide [descendTest, descendTestLead, executeOps, packingExecuteOp, wordOp, wordInstruction, hh, hp, hnode,
    BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  split <;> rename_i hz
  · rfl
  · congr 1

theorem descendTrace {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (size : Nat) (state : WordState bits) :
    (packingDynamicTrace rom containing (descendSteps size) state).length ≤ 1152 * (size + 1) := by
  have hh := packingDynamicTrace_length_le rom containing (descendSteps size) state
  unfold descendSteps at hh ⊢
  omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
