module

public import PaperProofs.Structure.PA17_ProgramTemplates_041k
public import Structure.PSTR_HD_WordSegments_014

/-! Concrete ordinary-word control macros for the fixed fullBuild lowering.
The physical control addresses are explicit.  No premise supplies a generated
program, a dimension ROM, an executed builder, or a protected cache. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

variable {bits : Nat}

def registerSlot (reg : Register) : Nat := 32 + reg.word

def virtualRegisters (heap : BitVec bits → BitVec bits) (reg : Register) : BitVec bits :=
  heap (BitVec.ofNat bits (registerSlot reg))

theorem registerSlot_bounds (reg : Register) :
    32 ≤ registerSlot reg ∧ registerSlot reg < 39 := by
  cases reg <;> decide

theorem registerSlot_injective : Function.Injective registerSlot := by
  intro left right h
  have hw : left.word = right.word := by unfold registerSlot at h; omega
  have hh := congrArg Register.fromWord hw
  simpa only [Register.fromWord_word, Option.some.injEq] using hh

def readControl (address : Nat) : List PackingOp :=
  [.base (.base (.constant .address address)),
   .base (.base (.loadHeap .value .address))]

def writeControl (address : Nat) : List PackingOp :=
  [.base (.base (.constant .address address)),
   .base (.base (.storeHeap .address .value))]

def readVirtual (reg : Register) : List PackingOp := readControl (registerSlot reg)
def writeVirtual (reg : Register) : List PackingOp := writeControl (registerSlot reg)

theorem readControl_length (address : Nat) : (readControl address).length = 2 := rfl
theorem writeControl_length (address : Nat) : (writeControl address).length = 2 := rfl

theorem readControl_straight (address : Nat) : StraightProgram (readControl address) := by
  simp [StraightProgram, readControl, StraightOp]

theorem writeControl_straight (address : Nat) : StraightProgram (writeControl address) := by
  simp [StraightProgram, writeControl, StraightOp]

theorem readControl_value (rom : PhysicalROM) (address : Nat) (state : WordState bits) :
    (executeOps rom (readControl address) state).register .value =
      state.heap (BitVec.ofNat bits address) := by
  simp [readControl, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem readControl_prefix_heap (rom : PhysicalROM) (address count : Nat)
    (state : WordState bits) :
    (executeOps rom ((readControl address).take count) state).heap = state.heap := by
  cases count with
  | zero => rfl
  | succ count => cases count <;>
      simp [readControl, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem writeControl_heap (rom : PhysicalROM) (address : Nat) (state : WordState bits) :
    (executeOps rom (writeControl address) state).heap =
      Function.update state.heap (BitVec.ofNat bits address) (state.register .value) := by
  simp [writeControl, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem writeControl_prefix_frame (rom : PhysicalROM) (address count : Nat)
    (state : WordState bits) (point : BitVec bits) (hne : point ≠ BitVec.ofNat bits address) :
    (executeOps rom ((writeControl address).take count) state).heap point = state.heap point := by
  cases count with
  | zero => rfl
  | succ count => cases count <;>
      simp [writeControl, executeOps, packingExecuteOp, wordOp, wordInstruction,
        Function.update_of_ne hne]

theorem writeControl_virtual (rom : PhysicalROM) (reg : Register) (state : WordState bits) :
    virtualRegisters (executeOps rom (writeVirtual reg) state).heap reg =
      state.register .value := by
  simp only [virtualRegisters, writeVirtual, writeControl_heap, Function.update_self]

theorem readControl_access (rom : PhysicalROM) (address heapWords count : Nat)
    (state : WordState bits) (ha : address < heapWords) (hc : count < 2) :
    packingAccessFits rom heapWords
      (executeOps rom ((readControl address).take count) state)
      ((readControl address)[count]'(by simpa only [readControl_length] using hc)) := by
  interval_cases count
  · trivial
  · change (BitVec.ofNat bits address).toNat < heapWords
    exact lt_of_le_of_lt (by simp only [BitVec.toNat_ofNat]; exact Nat.mod_le _ _) ha

theorem writeControl_access (rom : PhysicalROM) (address heapWords count : Nat)
    (state : WordState bits) (ha : address < heapWords) (hc : count < 2) :
    packingAccessFits rom heapWords
      (executeOps rom ((writeControl address).take count) state)
      ((writeControl address)[count]'(by simpa only [writeControl_length] using hc)) := by
  interval_cases count
  · trivial
  · change (BitVec.ofNat bits address).toNat < heapWords
    exact lt_of_le_of_lt (by simp only [BitVec.toNat_ofNat]; exact Nat.mod_le _ _) ha

/-- The supplied block is fetched from the containing fixed code, at its real PC.
This interface applies to all straight lowering macros and all their prefixes. -/
theorem straight_prefix (rom : PhysicalROM) (program block : List PackingOp)
    (start : Nat) (hbound : start + block.length ≤ program.length)
    (hcode : ∀ i (hi : i < block.length), program[start + i]'(by omega) = block[i])
    (hstraight : StraightProgram block) (hwords : WordsFit bits (packingCode program))
    (hpcfit : Fits bits (5 * program.length)) (state : WordState bits)
    (hpc : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ block.length) :
    packingRun rom program count state = executeOps rom (block.take count) state := by
  have hl : (block.take count).length = count := List.length_take_of_le hc
  conv_lhs => rw [← hl]
  apply PSTRWordSegments.straight_segment rom program (block.take count) start
    (by omega) ?_ ?_ hwords hpcfit state hpc ha
  · intro i hi
    have hi' : i < block.length := by rw [hl] at hi; omega
    simpa only [List.getElem_take] using hcode i hi'
  · intro op ho
    exact hstraight op (List.mem_of_mem_take ho)

/-- Real raw-input dimension loads; the producer's actual .old register is saved
as t.  In particular raw input[2] is never mistaken for a dimension.  A caller
must preserve or move any live cache at physical addresses 0,1,2 first. -/
def initDimensions : List PackingOp :=
  [.base (.base (.constant .address 0)),
   .base (.base (.loadROM .input .value .address)),
   .base (.base (.storeHeap .address .value)),
   .base (.base (.constant .address 1)),
   .base (.base (.loadROM .input .value .address)),
   .base (.base (.storeHeap .address .value)),
   .base (.base (.constant .address 2)),
   .base (.base (.storeHeap .address .old))]

theorem initDimensions_length : initDimensions.length = 8 := rfl

theorem initDimensions_straight : StraightProgram initDimensions := by
  simp [StraightProgram, initDimensions, StraightOp]

/-- Exact machine result, valid even at small bit widths; disjointness of
control words is deliberately not assumed in this equation. -/
theorem initDimensions_heap (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom initDimensions state).heap =
      Function.update
        (Function.update
          (Function.update state.heap (BitVec.ofNat bits 0)
            (BitVec.ofNat bits (rom.input.getD (BitVec.ofNat bits 0).toNat 0)))
          (BitVec.ofNat bits 1)
            (BitVec.ofNat bits (rom.input.getD (BitVec.ofNat bits 1).toNat 0)))
        (BitVec.ofNat bits 2) (state.register .old) := by
  simp [initDimensions, executeOps, packingExecuteOp, wordOp, wordInstruction,
    PhysicalROM.words]

theorem initDimensions_prefix_frame (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 8) (point : BitVec bits)
    (h0 : point ≠ BitVec.ofNat bits 0) (h1 : point ≠ BitVec.ofNat bits 1)
    (h2 : point ≠ BitVec.ofNat bits 2) :
    (executeOps rom (initDimensions.take count) state).heap point = state.heap point := by
  interval_cases count <;>
    simp [initDimensions, executeOps, packingExecuteOp, wordOp, wordInstruction,
      Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2]

theorem initDimensions_old (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom initDimensions state).register .old = state.register .old := by
  simp [initDimensions, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem initDimensions_access (rom : PhysicalROM) (state : WordState bits)
    (heapWords count : Nat) (hrom : 2 ≤ rom.input.length) (hheap : 3 ≤ heapWords)
    (hc : count < 8) :
    packingAccessFits rom heapWords
      (executeOps rom (initDimensions.take count) state)
      (initDimensions[count]'(by simpa only [initDimensions_length] using hc)) := by
  have h0 : (BitVec.ofNat bits 0).toNat < 1 := by simp
  have h1 : (BitVec.ofNat bits 1).toNat ≤ 1 := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_le _ _
  have h2 : (BitVec.ofNat bits 2).toNat ≤ 2 := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_le _ _
  simp only [BitVec.toNat_ofNat] at h0 h1 h2
  interval_cases count <;>
    simp [initDimensions, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, PhysicalROM.words] <;> omega

theorem straight_prefix_control (rom : PhysicalROM) (block : List PackingOp)
    (hstraight : StraightProgram block) (state : WordState bits) (count : Nat) :
    (executeOps rom (block.take count) state).pc =
        state.pc + BitVec.ofNat bits (5 * min count block.length) ∧
      (executeOps rom (block.take count) state).halted = state.halted := by
  refine ⟨?_, executeOps_halted rom _ state⟩
  rw [executeOps_pc rom _ state (fun op ho => hstraight op (List.mem_of_mem_take ho)),
    List.length_take]

theorem actual_trace_bound (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) (count : Nat) :
    (packingDynamicTrace rom program count state).length ≤ 12 * count :=
  PA17UniformGenerator035a.dynamicTrace_length_le rom program bits count state

end PaperProofs.Structure.LaminarTree.PSTRBuildLower
