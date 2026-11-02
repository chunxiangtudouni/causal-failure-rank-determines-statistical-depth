module

public import Structure.PSTR_ReplyCapacity_025
public import Structure.PSTR_HD_WordSegments_014

/-! Actual initialization of the MAIN count-pass scratch W+12..W+15.
The metadata-end locator is a separate preceding block. It preserves old
and fresh, so width/mask are parked in those ordinary registers beforehand.
The existing genuine four-store spill is reused; no scratch input is assumed. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountInit

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open PSTRReplySpill

def park : List PackingOp :=
  [.base (.base (.constant .address 0)),
   .base (.base (.add .old .total .address)),
   .base (.base (.add .fresh .flag .address))]

def head : List PackingOp :=
  [.base (.base (.constant .flag 0)),
   .base (.base (.add .value .old .flag)),
   .base (.base (.add .old .fresh .flag)),
   .base (.base (.constant .fresh 0)),
   .base (.base (.constant .index 0)),
   .base (.base (.constant .flag 12)),
   .base (.base (.add .flag .address .flag))]

def tail : List PackingOp :=
  [.base (.base (.constant .total 16)),
   .base (.base (.add .old .address .total)),
   .base (.base (.constant .value 0))]

def program : List PackingOp := head ++ spillProgram ++ tail

theorem park_length : park.length = 3 := rfl
theorem head_length : head.length = 7 := rfl
theorem tail_length : tail.length = 3 := rfl
theorem program_length : program.length = 18 := rfl
theorem park_straight : StraightProgram park := by simp [park, StraightProgram, StraightOp]
theorem head_straight : StraightProgram head := by simp [head, StraightProgram, StraightOp]
theorem tail_straight : StraightProgram tail := by simp [tail, StraightProgram, StraightOp]
theorem program_straight : StraightProgram program := by
  simp [program, head, spillProgram, tail, StraightProgram, StraightOp]

theorem park_registers {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom park state).register .old = state.register .total ∧
    (executeOps rom park state).register .fresh = state.register .flag ∧
    (executeOps rom park state).register .value = state.register .value ∧
    (executeOps rom park state).register .index = state.register .index ∧
    (executeOps rom park state).heap = state.heap := by
  simp +decide only [park, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, BitVec.add_zero, and_self]

theorem head_registers {bits : Nat} (rom : PhysicalROM) (workspace : Nat) (state : WordState bits)
    (ha : state.register .address = BitVec.ofNat bits workspace) :
    (executeOps rom head state).register .value = state.register .old ∧
    (executeOps rom head state).register .old = state.register .fresh ∧
    (executeOps rom head state).register .fresh = BitVec.ofNat bits 0 ∧
    (executeOps rom head state).register .index = BitVec.ofNat bits 0 ∧
    (executeOps rom head state).register .flag = BitVec.ofNat bits (workspace + 12) ∧
    (executeOps rom head state).register .address = state.register .address ∧
    (executeOps rom head state).heap = state.heap := by
  simp +decide only [head, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, BitVec.add_zero, ha, BitVec.ofNat_add_ofNat, and_self]

theorem tail_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom tail state).heap = state.heap := rfl

theorem head_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 7) :
    (executeOps rom (head.take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem tail_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) : (executeOps rom (tail.take count) state).heap = state.heap := by
  by_cases hc : count ≤ 3
  · interval_cases count <;> rfl
  · rw [List.take_of_length_le (show tail.length ≤ count by rw [tail_length]; omega)]
    exact tail_heap rom state

theorem execute_heap {bits : Nat} (rom : PhysicalROM) (workspace : Nat) (state : WordState bits)
    (ha : state.register .address = BitVec.ofNat bits workspace) :
    (executeOps rom program state).heap = spillHeap (workspace + 12) (executeOps rom head state) := by
  rw [program, executeOps_append, executeOps_append, tail_heap]
  exact spill_execute_heap rom (executeOps rom head state) _ (head_registers rom workspace state ha).2.2.2.2.1

theorem execute_frame {bits : Nat} (rom : PhysicalROM) (workspace : Nat) (state : WordState bits)
    (ha : state.register .address = BitVec.ofNat bits workspace)
    (hroom : Fits bits (workspace + 15)) (address : Nat) (haddress : address < workspace + 12) :
    (executeOps rom program state).heap (BitVec.ofNat bits address) = state.heap (BitVec.ofNat bits address) := by
  have hfit : Fits bits address := (show address ≤ workspace + 15 by omega).trans_lt hroom
  have hs : Fits bits ((workspace + 12) + 3) := by simpa only [Nat.add_assoc] using hroom
  rw [execute_heap rom workspace state ha, spill_frame (workspace + 12) _ hs address hfit haddress,
    (head_registers rom workspace state ha).2.2.2.2.2.2]

theorem execute_slots {bits : Nat} (rom : PhysicalROM) (workspace : Nat) (state : WordState bits)
    (ha : state.register .address = BitVec.ofNat bits workspace)
    (hroom : Fits bits (workspace + 15)) (offset : Nat) (hoffset : offset < 4) :
    (executeOps rom program state).heap (BitVec.ofNat bits (workspace + 12 + offset)) =
      if offset = 0 then state.register .old
      else if offset = 1 then state.register .fresh else BitVec.ofNat bits 0 := by
  have hs : Fits bits ((workspace + 12) + 3) := by simpa only [Nat.add_assoc] using hroom
  have regs := head_registers rom workspace state ha
  rw [execute_heap rom workspace state ha, spill_slot (workspace + 12) _ hs offset hoffset]
  interval_cases offset <;> simp +decide only [savedWord, regs.1, regs.2.1, regs.2.2.1, regs.2.2.2.1, ↓reduceIte]

theorem prefix_frame {bits : Nat} (rom : PhysicalROM) (workspace : Nat) (state : WordState bits)
    (ha : state.register .address = BitVec.ofNat bits workspace)
    (hroom : Fits bits (workspace + 15)) (address : Nat) (haddress : address < workspace + 12)
    (count : Nat) :
    (executeOps rom (program.take count) state).heap (BitVec.ofNat bits address) =
      state.heap (BitVec.ofNat bits address) := by
  have hs : Fits bits ((workspace + 12) + 3) := by simpa only [Nat.add_assoc] using hroom
  have regs := head_registers rom workspace state ha
  change (executeOps rom ((head ++ (spillProgram ++ tail)).take count) state).heap
    (BitVec.ofNat bits address) = state.heap (BitVec.ofNat bits address)
  by_cases hfirst : count ≤ 7
  · rw [List.take_append_of_le_length (show count ≤ head.length from hfirst),
      head_prefix_heap rom state count hfirst]
  · rw [List.take_append,
      List.take_of_length_le (show head.length ≤ count by rw [head_length]; omega),
      executeOps_append, head_length]
    by_cases hspill : count - 7 ≤ 8
    · rw [List.take_append_of_le_length (show count - 7 ≤ spillProgram.length from hspill)]
      exact (PSTRReplyCapacity.spill_prefix_frame rom (executeOps rom head state) (workspace + 12)
        regs.2.2.2.2.1 hs address haddress (count - 7) hspill).trans (congrFun regs.2.2.2.2.2.2 _)
    · rw [List.take_append,
        List.take_of_length_le (show spillProgram.length ≤ count - 7 by rw [spill_length]; omega),
        executeOps_append, tail_prefix_heap]
      have hh := PSTRReplyCapacity.spill_prefix_frame rom (executeOps rom head state) (workspace + 12)
        regs.2.2.2.2.1 hs address haddress 8 le_rfl
      rw [List.take_of_length_le (show spillProgram.length ≤ 8 by rw [spill_length])] at hh
      exact hh.trans (congrFun regs.2.2.2.2.2.2 _)

set_option maxRecDepth 6000 in
theorem execute_registers {bits : Nat} (rom : PhysicalROM) (workspace : Nat) (state : WordState bits)
    (ha : state.register .address = BitVec.ofNat bits workspace) :
    (executeOps rom program state).register .old = BitVec.ofNat bits (workspace + 16) ∧
    (executeOps rom program state).register .index = BitVec.ofNat bits 0 ∧
    (executeOps rom program state).register .fresh = BitVec.ofNat bits 0 ∧
    (executeOps rom program state).register .value = BitVec.ofNat bits 0 := by
  simp +decide only [program, head, spillProgram, tail, List.cons_append, List.nil_append,
    executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
    ha, BitVec.ofNat_add_ofNat, and_self]

theorem containing_park {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + park.length ≤ whole.length)
    (hcode : ∀ i (hi : i < park.length), whole[start + i]'(by omega) = park[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 3 state = executeOps rom park state :=
  PSTRWordSegments.straight_segment rom whole park start hbound hcode park_straight hw hpcfit state hp ha

theorem containing_init {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + program.length ≤ whole.length)
    (hcode : ∀ i (hi : i < program.length), whole[start + i]'(by omega) = program[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 18 state = executeOps rom program state :=
  PSTRWordSegments.straight_segment rom whole program start hbound hcode program_straight hw hpcfit state hp ha

theorem trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 18 state).length ≤ 216 :=
  packingDynamicTrace_length_le rom whole 18 state

end PaperProofs.Structure.LaminarTree.PSTRCountInit
