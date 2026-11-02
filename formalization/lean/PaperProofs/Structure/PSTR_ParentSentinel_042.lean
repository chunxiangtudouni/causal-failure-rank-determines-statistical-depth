module

public import PaperProofs.Structure.PSTR_QueryLayout_041
public import PaperProofs.Structure.PSTR_ReplyCapacity_025
public import PaperProofs.Structure.PSTR_HD_WordSegments_014

/-! A real five-op initialization of the parent sentinel AFTER the counts
array. t is actually loaded from physical header0. The cached edgeCount word
is not used as the sentinel. The remaining t parent words are copied by the
outer traversal, separately; this block alone is not ParentHeapFor. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRParentSentinel

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM
open PSTRQueryLayout

def program : List PackingOp :=
  [.base (.base (.constant .address 0)),
   .base (.base (.loadHeap .total .address)),
   .base (.base (.add .flag .old .total)),
   .base (.base (.constant .index 0)),
   .base (.base (.storeHeap .flag .index))]

theorem program_length : program.length = 5 := rfl
theorem program_straight : StraightProgram program := by simp [program, StraightProgram, StraightOp]

theorem execute_heap {bits : Nat} (rom : PhysicalROM) (workspace size : Nat) (state : WordState bits)
    (hb : state.register .old = BitVec.ofNat bits (countsBase workspace))
    (ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size) :
    (executeOps rom program state).heap =
      Function.update state.heap (BitVec.ofNat bits (parentsBase workspace size)) (BitVec.ofNat bits 0) := by
  simp +decide only [program, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hb, ht, BitVec.ofNat_add_ofNat, parentsBase]

theorem execute_registers {bits : Nat} (rom : PhysicalROM) (workspace size : Nat) (state : WordState bits)
    (hb : state.register .old = BitVec.ofNat bits (countsBase workspace))
    (ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size) :
    (executeOps rom program state).register .flag = BitVec.ofNat bits (parentsBase workspace size) ∧
      (executeOps rom program state).register .old = state.register .old ∧
      (executeOps rom program state).register .fresh = state.register .fresh ∧
      (executeOps rom program state).register .value = state.register .value ∧
      (executeOps rom program state).register .index = BitVec.ofNat bits 0 := by
  simp +decide only [program, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hb, ht, BitVec.ofNat_add_ofNat, parentsBase, and_self]

theorem sentinel {bits : Nat} (rom : PhysicalROM) (workspace size : Nat) (state : WordState bits)
    (hb : state.register .old = BitVec.ofNat bits (countsBase workspace))
    (ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size) :
    (executeOps rom program state).heap (BitVec.ofNat bits (parentsBase workspace size)) = BitVec.ofNat bits 0 := by
  rw [execute_heap rom workspace size state hb ht, Function.update_self]

theorem frame {bits : Nat} (rom : PhysicalROM) (workspace size : Nat) (state : WordState bits)
    (hb : state.register .old = BitVec.ofNat bits (countsBase workspace))
    (ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size)
    (hroom : Fits bits (parentsBase workspace size)) (address : Nat)
    (ha : address < parentsBase workspace size) :
    (executeOps rom program state).heap (BitVec.ofNat bits address) = state.heap (BitVec.ofNat bits address) := by
  have hfit : Fits bits address := ha.trans hroom
  have hne : BitVec.ofNat bits address ≠ BitVec.ofNat bits (parentsBase workspace size) :=
    (ofNat_injective_of_fit _ _ hfit hroom).not.mpr (by omega)
  rw [execute_heap rom workspace size state hb ht, Function.update_of_ne hne]

theorem prefix_frame {bits : Nat} (rom : PhysicalROM) (workspace size : Nat) (state : WordState bits)
    (hb : state.register .old = BitVec.ofNat bits (countsBase workspace))
    (ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size)
    (hroom : Fits bits (parentsBase workspace size)) (address : Nat)
    (ha : address < parentsBase workspace size) (count : Nat) (hc : count ≤ 5) :
    (executeOps rom (program.take count) state).heap (BitVec.ofNat bits address) =
      state.heap (BitVec.ofNat bits address) := by
  by_cases hlast : count = 5
  · subst count
    rw [List.take_of_length_le (show program.length ≤ 5 by rw [program_length])]
    exact frame rom workspace size state hb ht hroom address ha
  · have hbefore : count ≤ 4 := by omega
    interval_cases count <;> rfl

theorem containing_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + program.length ≤ whole.length)
    (hcode : ∀ i (hi : i < program.length), whole[start + i]'(by omega) = program[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 5 state = executeOps rom program state :=
  PSTRWordSegments.straight_segment rom whole program start hbound hcode program_straight hw hpcfit state hp ha

theorem trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 5 state).length ≤ 60 :=
  packingDynamicTrace_length_le rom whole 5 state

end PaperProofs.Structure.LaminarTree.PSTRParentSentinel
