module

public import Structure.PA17_A19QueryBridge_RuntimeRanks_008g

/-! Fixed firstSlackChild-candidate initialization for the runtime selector.
This is the selector's child-pointer array, NOT PSTR's parent-sentinel copy.
t is read from actual physical header0, q from original ROM input1; the
header pointer is retained. The program is fixed before N/q/t/bits and uses
one actual jump loop, with ACTIVE fall-through and no scratch heap. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM

def clearSetup : List PackingOp :=
  [.base (.base (.constant .index 0)), .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .flag 1)), .base (.base (.add .total .total .flag)),
   .base (.base (.constant .index 1)), .base (.base (.loadROM .input .fresh .index)),
   .base (.base (.constant .flag 2)), .base (.base (.add .fresh .fresh .flag)),
   .base (.base (.constant .index 16)), .base (.base (.add .index .address .index)),
   .base (.base (.add .index .index .fresh)), .base (.base (.add .index .index .fresh)),
   .base (.base (.constant .value 0)), .base (.base (.constant .flag 1))]

def clearTestLead (origin : Nat) : List PackingOp :=
  [.base (.base (.constant .old (5 * (origin + 21))))]

def clearTest (origin : Nat) : List PackingOp := clearTestLead origin ++ [.jumpIfZero .total .old]

def clearBodyLead (origin : Nat) : List PackingOp :=
  [.base (.base (.storeHeap .index .value)), .base (.base (.add .index .index .flag)),
   .base (.subtract .total .total .flag), .base (.base (.constant .old (5 * (origin + 14))))]

def clearBody (origin : Nat) : List PackingOp := clearBodyLead origin ++ [.jumpIfZero .value .old]

def clearProgramAt (origin : Nat) : List PackingOp := clearSetup ++ clearTest origin ++ clearBody origin

def childBase (header q : Nat) : Nat := header + 16 + 2 * (q + 2)
def clearSteps (size : Nat) : Nat := 7 * (size + 1) + 16

theorem clearSetup_length : clearSetup.length = 14 := rfl
theorem clearTestLead_length (origin : Nat) : (clearTestLead origin).length = 1 := rfl
theorem clearTest_length (origin : Nat) : (clearTest origin).length = 2 := rfl
theorem clearBodyLead_length (origin : Nat) : (clearBodyLead origin).length = 4 := rfl
theorem clearBody_length (origin : Nat) : (clearBody origin).length = 5 := rfl
theorem clearProgramAt_length (origin : Nat) : (clearProgramAt origin).length = 21 := rfl

theorem clearSetup_straight : StraightProgram clearSetup := by simp [clearSetup, StraightProgram, StraightOp]
theorem clearTestLead_straight (origin : Nat) : StraightProgram (clearTestLead origin) := by
  simp [clearTestLead, StraightProgram, StraightOp]
theorem clearBodyLead_straight (origin : Nat) : StraightProgram (clearBodyLead origin) := by
  simp [clearBodyLead, StraightProgram, StraightOp]

theorem clearSetup_result {bits : Nat} (rom : PhysicalROM) (q size header : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hq : (rom.words .input).getD 1 0 = q) (hh : state.register .address = BitVec.ofNat bits header) :
    let after := executeOps rom clearSetup state
    after.register .address = BitVec.ofNat bits header ∧
      after.register .total = BitVec.ofNat bits (size + 1) ∧
      after.register .fresh = BitVec.ofNat bits (q + 2) ∧
      after.register .index = BitVec.ofNat bits (childBase header q) ∧
      after.register .value = BitVec.ofNat bits 0 ∧ after.register .flag = BitVec.ofNat bits 1 ∧ after.heap = state.heap := by
  change (rom.words .input)[1]?.getD 0 = q at hq
  have ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    have he := congrArg (BitVec.ofNat bits) hsize
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using he
  simp +decide [clearSetup, childBase, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hh, ht, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, BitVec.ofNat_add_ofNat]
  congr 1
  omega

theorem clearBody_result {bits : Nat} (rom : PhysicalROM) (origin remaining pointer : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hr : Fits bits (remaining + 1))
    (hi : state.register .index = BitVec.ofNat bits pointer)
    (ht : state.register .total = BitVec.ofNat bits (remaining + 1))
    (hv : state.register .value = BitVec.ofNat bits 0) (hf : state.register .flag = BitVec.ofNat bits 1) :
    let after := executeOps rom (clearBody origin) state
    after.heap = Function.update state.heap (BitVec.ofNat bits pointer) (BitVec.ofNat bits 0) ∧
      after.register .index = BitVec.ofNat bits (pointer + 1) ∧
      after.register .total = BitVec.ofNat bits remaining ∧
      after.register .address = state.register .address ∧ after.register .value = BitVec.ofNat bits 0 ∧
      after.register .flag = BitVec.ofNat bits 1 ∧ after.pc = BitVec.ofNat bits (5 * (origin + 14)) := by
  simp +decide [clearBody, clearBodyLead, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hi, ht, hv, hf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hr, BitVec.ofNat_add_ofNat]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
