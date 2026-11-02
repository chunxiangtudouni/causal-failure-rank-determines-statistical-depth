module

public import Structure.PSTR_BuildLower_Ordinary_016
public import Structure.PSTR_BuildLower_AST_014

/-! Static double-cutoff dispatcher syntax and the actual comparison prefix.
Packed bodies are static code parameters until the real A06 backend is frozen;
this definition asserts no correctness oracle for those bodies. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  PA17ProgramTemplates041

variable {bits : Nat}

def memoryClassify (pointer : Register) (ordinaryPC : Nat) : List PackingOp :=
  relativeRead (registerOffset pointer) .old ++ relativeRead 3 .fresh ++
    [.base (.subtract .flag .fresh .old),
     .base (.base (.constant .fresh ordinaryPC)), .jumpIfZero .flag .fresh]

theorem memoryClassify_length (pointer : Register) (ordinaryPC : Nat) :
    (memoryClassify pointer ordinaryPC).length = 9 := rfl

theorem memoryClassify_old (rom : PhysicalROM) (pointer : Register) (ordinaryPC : Nat)
    (state : WordState bits) :
    (executeOps rom (memoryClassify pointer ordinaryPC) state).register .old =
      Ordinary.pointerValue state pointer := by
  simp [memoryClassify, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Ordinary.pointerValue]

theorem memoryClassify_value (rom : PhysicalROM) (pointer : Register) (ordinaryPC : Nat)
    (state : WordState bits) :
    (executeOps rom (memoryClassify pointer ordinaryPC) state).register .value = state.register .value := rfl

theorem memoryClassify_pc (rom : PhysicalROM) (pointer : Register) (ordinaryPC : Nat)
    (state : WordState bits) :
    (executeOps rom (memoryClassify pointer ordinaryPC) state).pc =
      if (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤
          (Ordinary.pointerValue state pointer).toNat then BitVec.ofNat bits ordinaryPC
      else state.pc + BitVec.ofNat bits 45 := by
  change (executeOps rom (memoryClassify pointer ordinaryPC) state).pc =
    if (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤
        (state.heap (state.register .address + BitVec.ofNat bits (registerOffset pointer))).toNat then
      BitVec.ofNat bits ordinaryPC else state.pc + BitVec.ofNat bits 45
  have hsmall : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat -
      (state.heap (state.register .address + BitVec.ofNat bits (registerOffset pointer))).toNat < 2 ^ bits :=
    (Nat.sub_le _ _).trans_lt (state.heap _).isLt
  simp [memoryClassify, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall, Nat.sub_eq_zero_iff_le,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem memoryClassify_prefix_frame (rom : PhysicalROM) (pointer : Register) (ordinaryPC : Nat)
    (state : WordState bits) (count : Nat) :
    (executeOps rom ((memoryClassify pointer ordinaryPC).take count) state).heap = state.heap ∧
      (executeOps rom ((memoryClassify pointer ordinaryPC).take count) state).register .address =
        state.register .address := by
  by_cases hc : count ≤ 9
  · interval_cases count <;>
      simp [memoryClassify, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]
  · rw [List.take_of_length_le (by rw [memoryClassify_length]; omega)]
    exact ⟨rfl, rfl⟩

def forwardJump (nextPC : Nat) : List PackingOp :=
  [.base (.base (.constant .flag 0)),
   .base (.base (.constant .fresh nextPC)), .jumpIfZero .flag .fresh]

theorem forwardJump_length (nextPC : Nat) : (forwardJump nextPC).length = 3 := rfl

theorem forwardJump_pc (rom : PhysicalROM) (nextPC : Nat) (state : WordState bits) :
    (executeOps rom (forwardJump nextPC) state).pc = BitVec.ofNat bits nextPC := by
  simp [forwardJump, executeOps, packingExecuteOp, wordOp, wordInstruction]

def readDispatcher (packed : List PackingOp) (start : Nat) (pointer : Register) : List PackingOp :=
  memoryClassify pointer (5 * (start + 9 + packed.length + 3)) ++ packed ++
    forwardJump (5 * (start + 9 + packed.length + 3 + 12)) ++ Ordinary.read pointer

def writeDispatcher (packed : List PackingOp) (start : Nat) (pointer : Register) : List PackingOp :=
  memoryClassify pointer (5 * (start + 9 + packed.length + 3)) ++ packed ++
    forwardJump (5 * (start + 9 + packed.length + 3 + 12)) ++ Ordinary.write pointer

theorem readDispatcher_length (packed : List PackingOp) (start : Nat) (pointer : Register) :
    (readDispatcher packed start pointer).length = packed.length + 24 := by
  simp only [readDispatcher, List.length_append, memoryClassify_length, forwardJump_length, Ordinary.read_length]
  omega

theorem writeDispatcher_length (packed : List PackingOp) (start : Nat) (pointer : Register) :
    (writeDispatcher packed start pointer).length = packed.length + 24 := by
  simp only [writeDispatcher, List.length_append, memoryClassify_length, forwardJump_length, Ordinary.write_length]
  omega

def heapPorts (readROM : Nat → Region → Register → List PackingOp)
    (packedRead : List PackingOp) (packedWrite : Nat → List PackingOp) : BuilderPorts where
  readROM := readROM
  readHeap := readDispatcher packedRead
  writeHeap := fun start pointer => writeDispatcher (packedWrite (registerOffset pointer)) start pointer

def opReadsChildren : OpExpr → Bool
  | .literal (.base (.loadROM .children _ _)) => true
  | _ => false

def programReadsChildren : Program → Bool
  | .code ops => ops.any opReadsChildren
  | .append left right => programReadsChildren left || programReadsChildren right
  | .repeat _ _ body => programReadsChildren body

theorem fullBuild_no_children : programReadsChildren fullBuild = false := by decide

end PaperProofs.Structure.LaminarTree.PSTRBuildLower
