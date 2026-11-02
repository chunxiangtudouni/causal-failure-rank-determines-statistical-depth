module

public import Structure.PSTR_RuntimeRepair_017
import Mathlib.Tactic.IntervalCases

/-! Actual four-register spill/restore primitives for the old reply. The
spill preserves the marker's ordinary address/width registers. A later
wrapper must discharge the scratch frame through its actual update block. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRReplySpill

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM

def spillProgram : List PackingOp :=
  [.base (.base (.storeHeap .flag .value)),
   .base (.base (.constant .value 1)),
   .base (.base (.add .flag .flag .value)),
   .base (.base (.storeHeap .flag .old)),
   .base (.base (.add .flag .flag .value)),
   .base (.base (.storeHeap .flag .fresh)),
   .base (.base (.add .flag .flag .value)),
   .base (.base (.storeHeap .flag .index))]

def restoreProgram : List PackingOp :=
  [.base (.base (.constant .total 3)),
   .base (.subtract .flag .flag .total),
   .base (.base (.loadHeap .value .flag)),
   .base (.base (.constant .total 1)),
   .base (.base (.add .flag .flag .total)),
   .base (.base (.loadHeap .old .flag)),
   .base (.base (.add .flag .flag .total)),
   .base (.base (.loadHeap .fresh .flag)),
   .base (.base (.add .flag .flag .total)),
   .base (.base (.loadHeap .index .flag))]

def savedWord {bits : Nat} (state : WordState bits) : Nat → BitVec bits
  | 0 => state.register .value
  | 1 => state.register .old
  | 2 => state.register .fresh
  | _ => state.register .index

def spillHeap {bits : Nat} (base : Nat) (state : WordState bits) : BitVec bits → BitVec bits :=
  Function.update (Function.update (Function.update (Function.update state.heap
    (BitVec.ofNat bits base) (state.register .value))
    (BitVec.ofNat bits (base + 1)) (state.register .old))
    (BitVec.ofNat bits (base + 2)) (state.register .fresh))
    (BitVec.ofNat bits (base + 3)) (state.register .index)

def ReplyRegisters {bits : Nat} (before after : WordState bits) : Prop :=
  after.register .value = before.register .value ∧
  after.register .old = before.register .old ∧
  after.register .fresh = before.register .fresh ∧
  after.register .index = before.register .index

theorem spill_length : spillProgram.length = 8 := rfl

theorem restore_length : restoreProgram.length = 10 := rfl

theorem spill_straight : StraightProgram spillProgram := by
  simp [StraightProgram, StraightOp, spillProgram]

theorem restore_straight : StraightProgram restoreProgram := by
  simp [StraightProgram, StraightOp, restoreProgram]

theorem spill_address {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom spillProgram state).register .address = state.register .address := rfl

theorem spill_width {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom spillProgram state).register .total = state.register .total := rfl

theorem restore_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom restoreProgram state).heap = state.heap := rfl

theorem repair_cursor {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom PSTRRuntimeRepair.program state).register .flag = state.register .flag := rfl

theorem spill_execute_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (base : Nat)
    (hf : state.register .flag = BitVec.ofNat bits base) :
    (executeOps rom spillProgram state).heap = spillHeap base state := by
  have h2 : base + 1 + 1 = base + 2 := by omega
  have h3 : base + 2 + 1 = base + 3 := by omega
  simp +decide only [spillProgram, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hf, BitVec.ofNat_add_ofNat, h2, h3, spillHeap]

theorem spill_cursor {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (base : Nat)
    (hf : state.register .flag = BitVec.ofNat bits base) :
    (executeOps rom spillProgram state).register .flag = BitVec.ofNat bits (base + 3) := by
  have h2 : base + 1 + 1 = base + 2 := by omega
  have h3 : base + 2 + 1 = base + 3 := by omega
  simp +decide only [spillProgram, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hf, BitVec.ofNat_add_ofNat, h2, h3]

theorem slot_fit {bits : Nat} (base : Nat) (hs : Fits bits (base + 3))
    (offset : Nat) (ho : offset ≤ 3) : Fits bits (base + offset) := by
  exact (Nat.add_le_add_left ho base).trans_lt hs

theorem slot_injective {bits : Nat} (base : Nat) (hs : Fits bits (base + 3))
    (left right : Nat) (hl : left ≤ 3) (hr : right ≤ 3) :
    BitVec.ofNat bits (base + left) = BitVec.ofNat bits (base + right) ↔ left = right := by
  rw [ofNat_injective_of_fit _ _ (slot_fit base hs left hl) (slot_fit base hs right hr)]
  omega

theorem spill_slot {bits : Nat} (base : Nat) (state : WordState bits)
    (hs : Fits bits (base + 3)) (offset : Nat) (ho : offset < 4) :
    spillHeap base state (BitVec.ofNat bits (base + offset)) = savedWord state offset := by
  have hne (left right : Nat) (hl : left ≤ 3) (hr : right ≤ 3) (hn : left ≠ right) :
      BitVec.ofNat bits (base + left) ≠ BitVec.ofNat bits (base + right) :=
    (slot_injective base hs left right hl hr).not.mpr hn
  have h01 := hne 0 1 (by decide) (by decide) (by decide)
  have h02 := hne 0 2 (by decide) (by decide) (by decide)
  have h03 := hne 0 3 (by decide) (by decide) (by decide)
  have h12 := hne 1 2 (by decide) (by decide) (by decide)
  have h13 := hne 1 3 (by decide) (by decide) (by decide)
  have h23 := hne 2 3 (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at h01 h02 h03
  interval_cases offset <;>
    simp [spillHeap, savedWord, h01, h02, h03, h12, h13, h23]

theorem spill_frame {bits : Nat} (base : Nat) (state : WordState bits)
    (hs : Fits bits (base + 3)) (address : Nat) (ha : Fits bits address) (hbefore : address < base) :
    spillHeap base state (BitVec.ofNat bits address) = state.heap (BitVec.ofNat bits address) := by
  have hne (offset : Nat) (ho : offset ≤ 3) :
      BitVec.ofNat bits address ≠ BitVec.ofNat bits (base + offset) :=
    (ofNat_injective_of_fit _ _ ha (slot_fit base hs offset ho)).not.mpr (by omega)
  have hz := hne 0 (by decide)
  simp only [Nat.add_zero] at hz
  simp only [spillHeap, Function.update_apply, hne 3 (by decide), hne 2 (by decide),
    hne 1 (by decide), hz, ite_false]

set_option maxRecDepth 6000 in
theorem restore_reply {bits : Nat} (rom : PhysicalROM) (before current : WordState bits)
    (base : Nat) (hb : 8 ≤ bits) (hs : Fits bits (base + 3))
    (hf : current.register .flag = BitVec.ofNat bits (base + 3))
    (slots : ∀ offset < 4, current.heap (BitVec.ofNat bits (base + offset)) = savedWord before offset) :
    ReplyRegisters before (executeOps rom restoreProgram current) := by
  have hthree : 3 < 2 ^ bits := by have hh := Nat.lt_two_pow_self (n := bits); omega
  have hsub : base + 3 - 3 = base := by omega
  have h2 : base + 1 + 1 = base + 2 := by omega
  have h3 : base + 2 + 1 = base + 3 := by omega
  have h0 := slots 0 (by decide)
  have h1 := slots 1 (by decide)
  have hsecond := slots 2 (by decide)
  have hthird := slots 3 (by decide)
  simp only [Nat.add_zero, savedWord] at h0 h1 hsecond hthird
  simp +decide only [ReplyRegisters, restoreProgram, executeOps, packingExecuteOp, wordOp,
    wordInstruction, Function.update_apply, ↓reduceIte, hf, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hthree, hsub, BitVec.ofNat_add_ofNat,
    h2, h3, h0, h1, hsecond, hthird, and_self]

end PaperProofs.Structure.LaminarTree.PSTRReplySpill
