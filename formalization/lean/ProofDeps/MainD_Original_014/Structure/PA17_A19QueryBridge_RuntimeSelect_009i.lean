module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009h
public import Structure.PA17_A19QueryBridge_RuntimeSelect_009e
public import Structure.PA17_A19QueryBridge_RuntimeRead_007e

/-! The fixed reverse scan's actual assembly and independent continuations.
007 is invoked with only address=header and value=runtime payload pointer;
all its other register clobbers are permitted. No list is dimension-unrolled. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def reverseTestLead (origin : Nat) : List PackingOp :=
  [.base (.base (.constant .index 8)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .total .index)), .base (.base (.constant .old (5 * (origin + 105))))]

def reverseTest (origin : Nat) : List PackingOp := reverseTestLead origin ++ [.jumpIfZero .total .old]

def payloadRead : List PackingOp :=
  [.base (.base (.constant .index 8)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .old .index)), .base (.base (.constant .flag 1)),
   .base (.subtract .old .old .flag), .base (.base (.constant .index 9)),
   .base (.base (.add .index .address .index)), .base (.base (.loadHeap .value .index)),
   .base (.base (.add .value .value .old))]

def reverseFootLead (origin : Nat) : List PackingOp :=
  [.base (.base (.constant .index 8)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .total .index)), .base (.base (.constant .flag 1)),
   .base (.subtract .total .total .flag), .base (.base (.storeHeap .index .total)),
   .base (.base (.constant .old (5 * origin))), .base (.base (.constant .flag 0))]

def reverseFoot (origin : Nat) : List PackingOp := reverseFootLead origin ++ [.jumpIfZero .flag .old]

def reverseProgramAt (origin : Nat) : List PackingOp :=
  reverseTest origin ++ payloadRead ++ PA17A19RuntimeRead007.cachedProgram ++ pushProgram ++ reverseFoot origin

def parentProgramAt (origin : Nat) : List PackingOp :=
  clearProgramAt origin ++ preparePush ++ reverseProgramAt (origin + 59)

theorem reverseTestLead_length (origin : Nat) : (reverseTestLead origin).length = 4 := rfl
theorem reverseTest_length (origin : Nat) : (reverseTest origin).length = 5 := rfl
theorem payloadRead_length : payloadRead.length = 9 := rfl
theorem reverseFootLead_length (origin : Nat) : (reverseFootLead origin).length = 8 := rfl
theorem reverseFoot_length (origin : Nat) : (reverseFoot origin).length = 9 := rfl
theorem reverseProgramAt_length (origin : Nat) : (reverseProgramAt origin).length = 105 := rfl
theorem parentProgramAt_length (origin : Nat) : (parentProgramAt origin).length = 164 := rfl

theorem reverseTestLead_straight (origin : Nat) : StraightProgram (reverseTestLead origin) := by
  simp [reverseTestLead, StraightProgram, StraightOp]
theorem payloadRead_straight : StraightProgram payloadRead := by simp [payloadRead, StraightProgram, StraightOp]
theorem reverseFootLead_straight (origin : Nat) : StraightProgram (reverseFootLead origin) := by
  simp [reverseFootLead, StraightProgram, StraightOp]

theorem payloadRead_noStore : ∀ op ∈ payloadRead, HeapPreservingOp op := by simp [payloadRead, HeapPreservingOp]
theorem reverseTest_noStore (origin : Nat) : ∀ op ∈ reverseTest origin, HeapPreservingOp op := by
  simp [reverseTest, reverseTestLead, HeapPreservingOp]

theorem payloadRead_result {bits : Nat} (rom : PhysicalROM) (header base node : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hn : Fits bits (node + 1)) (hh : state.register .address = BitVec.ofNat bits header)
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (node + 1))
    (hbase : state.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits base) :
    let after := executeOps rom payloadRead state
    after.register .address = BitVec.ofNat bits header ∧ after.register .value = BitVec.ofNat bits (base + node) ∧
      after.heap = state.heap := by
  simp +decide [payloadRead, executeOps, packingExecuteOp, wordOp, wordInstruction, hh, hnode, hbase,
    BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hn]

theorem reverseFoot_result {bits : Nat} (rom : PhysicalROM) (origin header remaining : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hr : Fits bits (remaining + 1)) (hh : state.register .address = BitVec.ofNat bits header)
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (remaining + 1)) :
    let after := executeOps rom (reverseFoot origin) state
    after.register .address = BitVec.ofNat bits header ∧ after.register .total = BitVec.ofNat bits remaining ∧
      after.register .flag = BitVec.ofNat bits 0 ∧ after.pc = BitVec.ofNat bits (5 * origin) ∧
      after.heap = Function.update state.heap (BitVec.ofNat bits (header + 8)) (BitVec.ofNat bits remaining) := by
  simp +decide [reverseFoot, reverseFootLead, executeOps, packingExecuteOp, wordOp, wordInstruction, hh, hnode,
    BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hr]

theorem reverseTest_result {bits : Nat} (rom : PhysicalROM) (origin header remaining : Nat) (state : WordState bits)
    (hr : Fits bits remaining) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin))
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits remaining) :
    let after := executeOps rom (reverseTest origin) state
    after.pc = BitVec.ofNat bits (if remaining = 0 then 5 * (origin + 105) else 5 * (origin + 5)) ∧
      after.register .address = BitVec.ofNat bits header ∧ after.heap = state.heap := by
  simp +decide [reverseTest, reverseTestLead, executeOps, packingExecuteOp, wordOp, wordInstruction, hh, hp, hnode,
    BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  split <;> rename_i hz
  · rfl
  · congr 1

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
