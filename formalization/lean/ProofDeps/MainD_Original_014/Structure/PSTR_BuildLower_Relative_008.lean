module

public import Structure.PSTR_BuildLower_ValueOps_003

/-! Fixed code for a runtime control bank. The incoming actual hardware .address
register holds its base. All code literals are static offsets; the base never
appears in a constant instruction or the code-generation parameters. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM

variable {bits : Nat}

def relativeRead (offset : Nat) (target : Register) : List PackingOp :=
  [.base (.base (.constant .index offset)),
   .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap target .index))]

def relativeWrite (offset : Nat) : List PackingOp :=
  [.base (.base (.constant .index offset)),
   .base (.base (.add .index .address .index)),
   .base (.base (.storeHeap .index .value))]

theorem relativeRead_length (offset : Nat) (target : Register) :
    (relativeRead offset target).length = 3 := rfl

theorem relativeWrite_length (offset : Nat) : (relativeWrite offset).length = 3 := rfl

theorem relativeRead_straight (offset : Nat) (target : Register) :
    StraightProgram (relativeRead offset target) := by
  simp [relativeRead, StraightProgram, StraightOp]

theorem relativeWrite_straight (offset : Nat) : StraightProgram (relativeWrite offset) := by
  simp [relativeWrite, StraightProgram, StraightOp]

theorem relativeRead_code_fit (offset : Nat) (target : Register)
    (hsmall : Fits bits 8) (hoffset : Fits bits offset) :
    WordsFit bits (packingCode (relativeRead offset target)) := by
  intro value hvalue
  cases target <;>
    simp [packingCode, relativeRead, PackingOp.encode, Op.encodeWords,
      Instruction.encodeWords, Register.word, haltWords] at hvalue <;>
    simp only [Fits] at * <;> omega

theorem relativeWrite_code_fit (offset : Nat)
    (hsmall : Fits bits 8) (hoffset : Fits bits offset) :
    WordsFit bits (packingCode (relativeWrite offset)) := by
  intro value hvalue
  simp [packingCode, relativeWrite, PackingOp.encode, Op.encodeWords,
    Instruction.encodeWords, Register.word, haltWords] at hvalue
  simp only [Fits] at *
  omega

theorem relativeRead_value (rom : PhysicalROM) (offset : Nat) (target : Register)
    (state : WordState bits) :
    (executeOps rom (relativeRead offset target) state).register target =
      state.heap (state.register .address + BitVec.ofNat bits offset) := by
  simp [relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem relativeRead_prefix_heap (rom : PhysicalROM) (offset : Nat) (target : Register)
    (point : BitVec bits) : WordPrefixFrame rom (relativeRead offset target) point := by
  intro state count
  cases count with
  | zero => rfl
  | succ count => cases count with
    | zero => rfl
    | succ count => cases count <;>
        simp [relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem relativeRead_prefix_base (rom : PhysicalROM) (offset : Nat) (target : Register)
    (state : WordState bits) (ht : target ≠ .address) (count : Nat) :
    (executeOps rom ((relativeRead offset target).take count) state).register .address =
      state.register .address := by
  cases count with
  | zero => rfl
  | succ count => cases count with
    | zero => rfl
    | succ count => cases count <;>
        simp [relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
          Function.update_of_ne (Ne.symm ht)]

theorem relativeWrite_heap (rom : PhysicalROM) (offset : Nat) (state : WordState bits) :
    (executeOps rom (relativeWrite offset) state).heap =
      Function.update state.heap (state.register .address + BitVec.ofNat bits offset)
        (state.register .value) := by
  simp [relativeWrite, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem relativeWrite_prefix_frame (rom : PhysicalROM) (offset : Nat) (state : WordState bits)
    (point : BitVec bits) (hne : point ≠ state.register .address + BitVec.ofNat bits offset)
    (count : Nat) :
    (executeOps rom ((relativeWrite offset).take count) state).heap point = state.heap point := by
  cases count with
  | zero => rfl
  | succ count => cases count with
    | zero => rfl
    | succ count => cases count <;>
        simp [relativeWrite, executeOps, packingExecuteOp, wordOp, wordInstruction,
          Function.update_of_ne hne]

theorem relativeWrite_prefix_base (rom : PhysicalROM) (offset : Nat) (state : WordState bits)
    (count : Nat) :
    (executeOps rom ((relativeWrite offset).take count) state).register .address =
      state.register .address := by
  cases count with
  | zero => rfl
  | succ count => cases count with
    | zero => rfl
    | succ count => cases count <;>
        simp [relativeWrite, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem relativeRead_nat_value (rom : PhysicalROM) (offset : Nat) (target : Register)
    (state : NatState) :
    (runOps rom (relativeRead offset target) state).register target =
      state.heap (state.register .address + offset) := by
  simp [relativeRead, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem relativeWrite_nat_heap (rom : PhysicalROM) (offset : Nat) (state : NatState) :
    (runOps rom (relativeWrite offset) state).heap =
      Function.update state.heap (state.register .address + offset) (state.register .value) := rfl

end PaperProofs.Structure.LaminarTree.PSTRBuildLower
