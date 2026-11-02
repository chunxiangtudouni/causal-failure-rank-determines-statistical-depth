module

public import PaperProofs.Structure.PSTR_HD_CountFrameBlocks_039

/-! Composition rules for actual straight-block prefix accesses and physical
heap frames. These are proof rules over executeOps, not runtime operations. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

def HeapFrame {bits : Nat} (region : Nat → Prop)
    (old fresh : BitVec bits → BitVec bits) : Prop :=
  ∀ physical, Fits bits physical → region physical →
    fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical)

theorem heapFrame_refl {bits : Nat} (region : Nat → Prop) (heap : BitVec bits → BitVec bits) :
    HeapFrame region heap heap := by intro _ _ _; rfl

theorem heapFrame_trans {bits : Nat} (region : Nat → Prop)
    (first middle last : BitVec bits → BitVec bits)
    (hfm : HeapFrame region first middle) (hml : HeapFrame region middle last) :
    HeapFrame region first last := by
  intro physical hp hprotected
  exact (hml physical hp hprotected).trans (hfm physical hp hprotected)

structure PrefixOK {bits : Nat} (rom : PhysicalROM) (heapWords : Nat) (region : Nat → Prop)
    (ops : List PackingOp) (state : WordState bits) : Prop where
  access : ∀ count (hc : count < ops.length),
    packingAccessFits rom heapWords (executeOps rom (ops.take count) state) ops[count]
  frame : ∀ count ≤ ops.length, HeapFrame region state.heap (executeOps rom (ops.take count) state).heap

theorem take_append_after {bits : Nat} (rom : PhysicalROM) (left right : List PackingOp)
    (state : WordState bits) (count : Nat) (hleft : left.length ≤ count) :
    executeOps rom ((left ++ right).take count) state =
      executeOps rom (right.take (count - left.length)) (executeOps rom left state) := by
  rw [List.take_append, List.take_of_length_le hleft, executeOps_append]

theorem prefixOK_append {bits : Nat} (rom : PhysicalROM) (heapWords : Nat) (region : Nat → Prop)
    (left right : List PackingOp) (state : WordState bits)
    (hl : PrefixOK rom heapWords region left state)
    (hr : PrefixOK rom heapWords region right (executeOps rom left state)) :
    PrefixOK rom heapWords region (left ++ right) state := by
  constructor
  · intro count hc
    by_cases hcount : count < left.length
    · rw [List.take_append_of_le_length hcount.le, List.getElem_append_left hcount]
      exact hl.access count hcount
    · rw [take_append_after rom left right state count (by omega), List.getElem_append_right (by omega)]
      exact hr.access (count - left.length) (by rw [List.length_append] at hc; omega)
  · intro count hc
    by_cases hcount : count ≤ left.length
    · rw [List.take_append_of_le_length hcount]
      exact hl.frame count hcount
    · rw [take_append_after rom left right state count (by omega)]
      apply heapFrame_trans region state.heap (executeOps rom left state).heap _
      · simpa only [List.take_length] using hl.frame left.length le_rfl
      · exact hr.frame (count - left.length) (by rw [List.length_append] at hc; omega)

theorem readOnly_prefixOK {bits : Nat} (rom : PhysicalROM) (heapWords : Nat) (region : Nat → Prop)
    (ops : List PackingOp) (state : WordState bits) (ho : ∀ op ∈ ops, ReadOnly op)
    (ha : ∀ count (hc : count < ops.length),
      packingAccessFits rom heapWords (executeOps rom (ops.take count) state) ops[count]) :
    PrefixOK rom heapWords region ops state := by
  refine ⟨ha, ?_⟩
  intro count _hc
  rw [readOnly_prefix_heap rom ops state ho count]
  exact heapFrame_refl region state.heap

end PaperProofs.Structure.LaminarTree.PSTRCountKernel

