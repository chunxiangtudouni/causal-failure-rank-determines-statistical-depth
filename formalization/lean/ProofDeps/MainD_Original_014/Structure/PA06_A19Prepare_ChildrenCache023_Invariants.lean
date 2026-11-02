module

public import Structure.PA06_A19Prepare_ChildrenCache023_Iteration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateChildrenLayout RawCandidateChildrenPrefix

/-- The actual matched write is strictly before the final children end,
by the original prepared-tree edge count and ascending-prefix theory. -/
theorem matched_position_lt (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (CB parent child pointer : Nat) (state : NatState)
    (ready : InnerReady q full CB parent child pointer state)
    (hp : parent < preparedSize q full) (hc : child < preparedSize q full)
    (heq : parentWord q full child = parent + 1) :
    state.heap (CB + 66) < preparedSize q full - 1 := by
  have h := matched_write_lt_total (preparedSize q full) (parentWord q full) parent child hp hc heq
  have he := (exact_lists q full hq hl).2.2
  rw [he] at h
  rw [ready.flat_cell]
  simpa only [scanList, beforeList, rowList, List.length_append] using h

theorem bit_heap_frame (q : Nat) (full : List (Finset (Fin q))) (CB parent child : Nat)
    {before after : NatState} (hh : after.heap = bitHeap q full CB parent child before)
    (hwrite : parentWord q full child = parent + 1 → before.heap (CB + 66) < preparedSize q full - 1) :
    Frame q full CB before after := by
  intro address hout
  rw [hh]
  have htemp := hout.1
  by_cases heq : parentWord q full child = parent + 1
  · have hd := hwrite heq
    have hne : address ≠ childrenBase CB (mass q full) (preparedSize q full) + before.heap (CB + 66) := by
      rcases hout.2 with hout | hout <;> unfold childrenBase at * <;> omega
    simp only [bitHeap, ite_eq_left heq]
    rw [Function.update_of_ne (by omega : address ≠ CB + 65),
      Function.update_of_ne (by omega : address ≠ CB + 66),
      Function.update_of_ne (by omega : address ≠ CB + 69), Function.update_of_ne hne]
  · simp only [bitHeap, ite_eq_right heq]
    rw [Function.update_of_ne (by omega : address ≠ CB + 65)]

theorem scanList_zero (q : Nat) (full : List (Finset (Fin q))) (parent : Nat) :
    scanList q full parent 0 = beforeList q full parent := by
  simp only [scanList, rowList, childPrefix_zero, List.append_nil]

theorem scanList_succ (q : Nat) (full : List (Finset (Fin q))) (parent child : Nat) :
    scanList q full parent (child + 1) = if parentWord q full child = parent + 1 then
      scanList q full parent child ++ [child] else scanList q full parent child := by
  simp only [scanList, rowList, childPrefix_succ]
  split <;> simp only [List.append_assoc]

theorem scanList_full (q : Nat) (full : List (Finset (Fin q))) (parent : Nat) :
    scanList q full parent (preparedSize q full) = beforeList q full (parent + 1) := by
  simp only [scanList, rowList, beforeList, childPrefix_full, flatPrefix_succ]

theorem bit_heap_ready (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (CB parent child pointer nextPointer : Nat) {before after : NatState}
    (ready : InnerReady q full CB parent child pointer before)
    (hp : parent < preparedSize q full) (hc : child < preparedSize q full)
    (hh : after.heap = bitHeap q full CB parent child before)
    (hCB : after.register .address = before.register .address)
    (hpc : after.pc = nextPointer) (ha : after.halted = false) :
    InnerReady q full CB parent (child + 1) nextPointer after ∧ Frame q full CB before after := by
  have hwrite := matched_position_lt q full hq hl CB parent child pointer before ready hp hc
  have hf := bit_heap_frame q full CB parent child hh hwrite
  have hnewInput := ready.controls.input.of_frame hf hCB
  have hlarge : CB + 71 ≤ childrenBase CB (mass q full) (preparedSize q full) := by
    unfold childrenBase degreeBase
    omega
  have hslot (offset : Nat) (ho : offset = 67 ∨ offset = 68 ∨ offset = 70) :
      after.heap (CB + offset) = before.heap (CB + offset) := by
    rw [hh]
    rcases ho with rfl | rfl | rfl <;> by_cases heq : parentWord q full child = parent + 1 <;>
      simp (disch := omega) [bitHeap, heq]
  refine ⟨?_, hf⟩
  constructor
  · exact ⟨hnewInput, (hslot 67 (Or.inl rfl)).trans ready.controls.degree_base,
      (hslot 68 (Or.inr (Or.inl rfl))).trans ready.controls.children_base,
      (hslot 70 (Or.inr (Or.inr rfl))).trans ready.controls.size_cell, hpc, ha⟩
  · rw [hh]
    by_cases heq : parentWord q full child = parent + 1 <;>
      simpa (disch := omega) [bitHeap, heq, Function.update_apply] using ready.parent_cell
  · rw [hh]
    by_cases heq : parentWord q full child = parent + 1 <;> simp [bitHeap, heq]
  · rw [hh, rowList, childPrefix_length_succ]
    by_cases heq : parentWord q full child = parent + 1
    · simpa (disch := omega) [bitHeap, heq, rowList, Function.update_apply] using ready.degree_cell
    · simpa (disch := omega) [bitHeap, heq, rowList, Function.update_apply] using ready.degree_cell
  · rw [hh, scanList_succ]
    by_cases heq : parentWord q full child = parent + 1
    · simpa (disch := omega) [bitHeap, heq, Function.update_apply] using ready.flat_cell
    · simpa (disch := omega) [bitHeap, heq, Function.update_apply] using ready.flat_cell
  · intro node hn
    rw [hh]
    by_cases heq : parentWord q full child = parent + 1 <;>
      simpa (disch := omega) [bitHeap, heq, Function.update_apply, childrenBase, degreeBase] using ready.degrees node hn
  · rw [scanList_succ]
    by_cases heq : parentWord q full child = parent + 1
    · rw [ite_eq_left heq]
      apply RawCandidateSerializedChildrenRun.Written.snoc ready.children
      · intro position hposition
        rw [hh]
        have hne : childrenBase CB (mass q full) (preparedSize q full) + position ≠
            childrenBase CB (mass q full) (preparedSize q full) + before.heap (CB + 66) := by
          rw [ready.flat_cell]
          omega
        simp only [bitHeap, ite_eq_left heq]
        rw [Function.update_of_ne (by omega : childrenBase CB (mass q full) (preparedSize q full) + position ≠ CB + 65),
          Function.update_of_ne (by omega : childrenBase CB (mass q full) (preparedSize q full) + position ≠ CB + 66),
          Function.update_of_ne (by omega : childrenBase CB (mass q full) (preparedSize q full) + position ≠ CB + 69),
          Function.update_of_ne hne]
      · rw [hh]
        simp (disch := omega) [bitHeap, heq, ready.flat_cell]
    · rw [ite_eq_right heq]
      intro position hposition
      rw [hh]
      simpa (disch := omega) [bitHeap, heq, Function.update_apply] using ready.children position hposition

/-- One actual encoded iteration advances the exact ascending list invariant. -/
theorem child_iteration (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) (CB : Nat)
    (containing : List PackingOp) (start : Nat) (code : CodeAt containing start)
    (parent child : Nat) (state : NatState)
    (ready : InnerReady q full CB parent child (5 * (start + 49)) state)
    (hp : parent < preparedSize q full) (hc : child < preparedSize q full) :
    let after := natRun rom containing (iterationSteps (parentWord q full) parent child) state
    InnerReady q full CB parent (child + 1) (5 * (start + 49)) after ∧ Frame q full CB state after := by
  have hr := child_iteration_raw rom q full CB containing start code parent child state ready hc
  exact bit_heap_ready q full hq hl CB parent child _ _ ready hp hc hr.1
    (hr.2.1.trans ready.controls.input.address.symm) hr.2.2.1 hr.2.2.2

end PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
