module

public import Structure.PSTR_BuildLower_JumpAccess_122
public import Structure.PSTR_BuildLower_InlineAccess_120
public import Structure.PSTR_BuildLower_ConcreteAST_031

/-! The actual last-jump control blocks make only the proved finite bank
reads/stores. Classification and jumps remain real executed instructions;
no whole-body Nat-register bound is needed for direct Word access. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ControlAccess
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open RawTreePreprocessingClaims PA17PackedTranslator034
section Generic
variable {bits : Nat}

theorem classify_safe (physical : PhysicalROM) (pointer : Register) (target heapWords : Nat) (state : WordState bits)
    (pointerRoom : (state.register .address + BitVec.ofNat bits (registerOffset pointer)).toNat < heapWords)
    (cutoffRoom : (state.register .address + BitVec.ofNat bits 3).toNat < heapWords) :
    PackedAccessSafe heapWords physical (memoryClassify pointer target) state := by
  simp [BitVec.toNat_add] at pointerRoom cutoffRoom
  intro count hc
  change count < 9 at hc
  interval_cases count <;>
    simp [memoryClassify, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits]
  all_goals first | exact pointerRoom | exact cutoffRoom

theorem jump_safe (physical : PhysicalROM) (target heapWords : Nat) (state : WordState bits) :
    PackedAccessSafe heapWords physical (forwardJump target) state := by
  intro count hc
  change count < 3 at hc
  interval_cases count <;> trivial

theorem head_safe (physical : PhysicalROM) (counter target heapWords : Nat) (state : WordState bits)
    (room : (state.register .address + BitVec.ofNat bits counter).toNat < heapWords) :
    PackedAccessSafe heapWords physical (relativeLoopHead counter target) state := by
  simp [BitVec.toNat_add] at room
  intro count hc
  change count < 5 at hc
  interval_cases count <;>
    simp [relativeLoopHead, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits]
  exact room

theorem tail_safe (physical : PhysicalROM) (counter target heapWords : Nat) (state : WordState bits)
    (room : (state.register .address + BitVec.ofNat bits counter).toNat < heapWords) :
    PackedAccessSafe heapWords physical (relativeLoopTail counter target) state := by
  simp [BitVec.toNat_add] at room
  intro count hc
  change count < 9 at hc
  interval_cases count <;>
    simp [relativeLoopTail, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits]
  all_goals exact room

theorem input_head_safe (physical : PhysicalROM) (pointer : Register) (target heapWords : Nat) (state : WordState bits)
    (pointerRoom : (state.register .address + BitVec.ofNat bits (registerOffset pointer)).toNat < heapWords)
    (stageRoom : (state.register .address + BitVec.ofNat bits 0).toNat < heapWords)
    (toolRoom : (state.register .address + BitVec.ofNat bits 1).toNat < heapWords) :
    PackedAccessSafe heapWords physical (ConcreteAST.inputHead target pointer) state := by
  simp [BitVec.toNat_add] at pointerRoom stageRoom toolRoom
  intro count hc
  change count < 15 at hc
  interval_cases count <;>
    simp [ConcreteAST.inputHead, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits]
  all_goals first | exact pointerRoom | exact stageRoom | exact toolRoom

end Generic

theorem classify_actual_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (pointer : Register) (target : Nat) (left right : List PackingOp)
    (state : WordState (bits q full)) (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ memoryClassify pointer target ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ memoryClassify pointer target ++ right).length)) :
    TraceAccess.Safe (allocated q full) physical (left ++ memoryClassify pointer target ++ right) state 9 := by
  let lead := (memoryClassify pointer target).take 8
  have shape : lead ++ [.jumpIfZero .flag .fresh] = memoryClassify pointer target := rfl
  have hs : StraightProgram lead := by
    simp [lead, memoryClassify, relativeRead, StraightProgram, StraightOp]
  have localSafe : PackedAccessSafe (allocated q full) physical (memoryClassify pointer target) state :=
    classify_safe physical pointer target (allocated q full) state
      (BankAccess.point_room q full hq state base (registerOffset pointer)
        (by have hh := registerSlot_bounds pointer; change 32 ≤ registerOffset pointer ∧ registerOffset pointer < 39 at hh; omega))
      (BankAccess.point_room q full hq state base 3 (by decide))
  have result := AccessBridge.last_safe physical left lead right (.jumpIfZero .flag .fresh) (allocated q full) state hs
    (by rw [shape]; exact localSafe) hpc ha
    (by rw [shape]; exact hcode) (by rw [shape]; exact hpcfit)
  rw [shape] at result
  exact result

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ControlAccess
