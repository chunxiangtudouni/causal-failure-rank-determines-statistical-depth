module

public import Structure.PSTR_BuildLower_FixedExpr_010

/-! A fixed relative-address countdown head/tail. The counter offset and PC
labels are static syntax. The actual base stays in hardware.address. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM

variable {bits : Nat}

def relativeLoopHead (counter exit : Nat) : List PackingOp :=
  relativeRead counter .value ++
    [.base (.base (.constant .fresh exit)), .jumpIfZero .value .fresh]

def relativeLoopTail (counter entry : Nat) : List PackingOp :=
  relativeRead counter .value ++
    [.base (.base (.constant .old 1)),
     .base (.subtract .value .value .old),
     .base (.base (.storeHeap .index .value)),
     .base (.base (.constant .flag 0)),
     .base (.base (.constant .fresh entry)),
     .jumpIfZero .flag .fresh]

def relativeLoopBlock (counter start : Nat) (body : List PackingOp) : List PackingOp :=
  relativeLoopHead counter (5 * (start + body.length + 14)) ++ body ++
    relativeLoopTail counter (5 * start)

theorem relativeLoopHead_length (counter exit : Nat) :
    (relativeLoopHead counter exit).length = 5 := rfl

theorem relativeLoopTail_length (counter entry : Nat) :
    (relativeLoopTail counter entry).length = 9 := rfl

theorem relativeLoopBlock_length (counter start : Nat) (body : List PackingOp) :
    (relativeLoopBlock counter start body).length = body.length + 14 := by
  simp only [relativeLoopBlock, List.length_append, relativeLoopHead_length, relativeLoopTail_length]
  omega

theorem relativeLoopHead_word_heap (rom : PhysicalROM) (counter exit : Nat)
    (state : WordState bits) :
    (executeOps rom (relativeLoopHead counter exit) state).heap = state.heap := rfl

theorem relativeLoopHead_word_base (rom : PhysicalROM) (counter exit : Nat)
    (state : WordState bits) :
    (executeOps rom (relativeLoopHead counter exit) state).register .address =
      state.register .address := rfl

theorem relativeLoopHead_word_pc (rom : PhysicalROM) (counter exit : Nat)
    (state : WordState bits) :
    (executeOps rom (relativeLoopHead counter exit) state).pc =
      if (state.heap (state.register .address + BitVec.ofNat bits counter)).toNat = 0 then
        BitVec.ofNat bits exit else state.pc + BitVec.ofNat bits 25 := by
  simp [relativeLoopHead, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem relativeLoopTail_word_heap (rom : PhysicalROM) (counter entry : Nat)
    (state : WordState bits) :
    (executeOps rom (relativeLoopTail counter entry) state).heap =
      Function.update state.heap (state.register .address + BitVec.ofNat bits counter)
        (BitVec.ofNat bits
          ((state.heap (state.register .address + BitVec.ofNat bits counter)).toNat -
            (BitVec.ofNat bits 1).toNat)) := by
  simp [relativeLoopTail, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem relativeLoopTail_word_base (rom : PhysicalROM) (counter entry : Nat)
    (state : WordState bits) :
    (executeOps rom (relativeLoopTail counter entry) state).register .address =
      state.register .address := rfl

theorem relativeLoopTail_word_pc (rom : PhysicalROM) (counter entry : Nat)
    (state : WordState bits) :
    (executeOps rom (relativeLoopTail counter entry) state).pc = BitVec.ofNat bits entry := by
  simp [relativeLoopTail, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem relativeLoopHead_nat_pc (rom : PhysicalROM) (counter exit : Nat) (state : NatState) :
    (runOps rom (relativeLoopHead counter exit) state).pc =
      if state.heap (state.register .address + counter) = 0 then exit else state.pc + 25 := by
  simp [relativeLoopHead, relativeRead, runOps, natExecuteOp, Op.execute, Instruction.execute,
    Nat.add_assoc]

theorem relativeLoopTail_nat_heap (rom : PhysicalROM) (counter entry : Nat) (state : NatState) :
    (runOps rom (relativeLoopTail counter entry) state).heap =
      Function.update state.heap (state.register .address + counter)
        (state.heap (state.register .address + counter) - 1) := rfl

theorem relativeLoopTail_nat_pc (rom : PhysicalROM) (counter entry : Nat) (state : NatState) :
    (runOps rom (relativeLoopTail counter entry) state).pc = entry := rfl

theorem relativeLoopTail_nat_base (rom : PhysicalROM) (counter entry : Nat) (state : NatState) :
    (runOps rom (relativeLoopTail counter entry) state).register .address = state.register .address := rfl

end PaperProofs.Structure.LaminarTree.PSTRBuildLower
