module

public import Structure.PSTR_HD_SelectedActual_146

/-! Real8/6-op controller-only update programs. Only address/total/flag
are written: all four OLD reply registers survive EVERY prefix, without
spill, restore, scratch inputs or a reset. Existing bumpHeap/failHeap are
the exact physical effects of these newly allocated control registers. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRReplyControls
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PSTRReplySpill

def correctProgram : List PackingOp :=
  [.base (.base (.constant .address 2)),
   .base (.base (.loadHeap .address .address)),
   .base (.base (.constant .total 4)),
   .base (.base (.add .address .address .total)),
   .base (.base (.loadHeap .flag .address)),
   .base (.base (.constant .total 1)),
   .base (.base (.add .flag .flag .total)),
   .base (.base (.storeHeap .address .flag))]

def failProgram : List PackingOp :=
  [.base (.base (.constant .address 2)),
   .base (.base (.loadHeap .address .address)),
   .base (.base (.constant .total 5)),
   .base (.base (.add .address .address .total)),
   .base (.base (.constant .flag 1)),
   .base (.base (.storeHeap .address .flag))]

theorem correct_length : correctProgram.length = 8 := rfl
theorem fail_length : failProgram.length = 6 := rfl

theorem correct_straight : StraightProgram correctProgram := by simp [correctProgram, StraightProgram, StraightOp]
theorem fail_straight : StraightProgram failProgram := by simp [failProgram, StraightProgram, StraightOp]

theorem correct_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (packed : Nat)
    (header : (state.heap (BitVec.ofNat bits 2)).toNat = packed) :
    (executeOps rom correctProgram state).heap = PSTRRuntimeAdvance.bumpHeap packed state.heap := by
  have hc : packed + 4 = 4 + packed := by omega
  simp +decide only [correctProgram, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, PSTRRuntimeAdvance.header_word state packed header,
    BitVec.ofNat_add_ofNat, hc, PSTRRuntimeAdvance.bumpHeap]

theorem fail_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (packed : Nat)
    (header : (state.heap (BitVec.ofNat bits 2)).toNat = packed) :
    (executeOps rom failProgram state).heap = PSTRRuntimeFail.failHeap packed state.heap := by
  have hc : packed + 5 = 5 + packed := by omega
  simp +decide only [failProgram, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, PSTRRuntimeAdvance.header_word state packed header,
    BitVec.ofNat_add_ofNat, hc, PSTRRuntimeFail.failHeap]

theorem correct_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (packed : Nat)
    (header : (state.heap (BitVec.ofNat bits 2)).toNat = packed) (count : Nat) (hc : count ≤ 8) :
    (executeOps rom (correctProgram.take count) state).heap =
      if count < 8 then state.heap else PSTRRuntimeAdvance.bumpHeap packed state.heap := by
  by_cases h : count < 8
  · simp only [h, ite_true]
    interval_cases count <;> rfl
  · have he : count = 8 := by omega
    subst count
    simpa only [show 8 = correctProgram.length from rfl, List.take_length, Nat.lt_irrefl, ite_false] using correct_heap rom state packed header

theorem fail_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (packed : Nat)
    (header : (state.heap (BitVec.ofNat bits 2)).toNat = packed) (count : Nat) (hc : count ≤ 6) :
    (executeOps rom (failProgram.take count) state).heap =
      if count < 6 then state.heap else PSTRRuntimeFail.failHeap packed state.heap := by
  by_cases h : count < 6
  · simp only [h, ite_true]
    interval_cases count <;> rfl
  · have he : count = 6 := by omega
    subst count
    simpa only [show 6 = failProgram.length from rfl, List.take_length, Nat.lt_irrefl, ite_false] using fail_heap rom state packed header

theorem correct_prefix_registers {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 8) : ReplyRegisters state (executeOps rom (correctProgram.take count) state) := by
  interval_cases count <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem fail_prefix_registers {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 6) : ReplyRegisters state (executeOps rom (failProgram.take count) state) := by
  interval_cases count <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem correct_access {bits : Nat} (rom : PhysicalROM) (heapWords packed : Nat) (state : WordState bits)
    (header : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (fit : Fits bits (4 + packed)) (heapRoom : 4 + packed < heapWords)
    (count : Nat) (hc : count < correctProgram.length) :
    packingAccessFits rom heapWords (executeOps rom (correctProgram.take count) state) correctProgram[count] := by
  have h2 : (BitVec.ofNat bits 2).toNat < heapWords := (Nat.mod_le _ _).trans_lt (by omega)
  have hc4 : packed + 4 = 4 + packed := by omega
  change count < 8 at hc
  interval_cases count <;> try exact True.intro
  all_goals
    simp +decide only [correctProgram, List.take_succ_cons, List.take_zero,
      List.getElem_cons_zero, List.getElem_cons_succ, packingAccessFits, AccessFits,
      executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
      PSTRRuntimeAdvance.header_word state packed header, BitVec.ofNat_add_ofNat, hc4,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
    first | exact h2 | exact heapRoom

theorem fail_access {bits : Nat} (rom : PhysicalROM) (heapWords packed : Nat) (state : WordState bits)
    (header : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (fit : Fits bits (5 + packed)) (heapRoom : 5 + packed < heapWords)
    (count : Nat) (hc : count < failProgram.length) :
    packingAccessFits rom heapWords (executeOps rom (failProgram.take count) state) failProgram[count] := by
  have h2 : (BitVec.ofNat bits 2).toNat < heapWords := (Nat.mod_le _ _).trans_lt (by omega)
  have hc5 : packed + 5 = 5 + packed := by omega
  change count < 6 at hc
  interval_cases count <;> try exact True.intro
  all_goals
    simp +decide only [failProgram, List.take_succ_cons, List.take_zero,
      List.getElem_cons_zero, List.getElem_cons_succ, packingAccessFits, AccessFits,
      executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
      PSTRRuntimeAdvance.header_word state packed header, BitVec.ofNat_add_ofNat, hc5,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
    first | exact h2 | exact heapRoom

end PaperProofs.Structure.LaminarTree.PSTRReplyControls
