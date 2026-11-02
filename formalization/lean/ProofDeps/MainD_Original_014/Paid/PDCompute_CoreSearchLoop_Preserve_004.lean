module

public import Paid.PDCompute_CoreSearchLoop_Guard_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.CoreSearchLoop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver hiding HeapList
open PDMenu.ComputeFrame RootD27.Core
open PDLower.CalibrationCompute (HeapList)

theorem solvedBuffer_counter {P : Parameters} {fee penalty : ℚ} {upper : Bool} {before after : State}
    (represented : SolvedBuffer P fee penalty upper before) (memory : RegionMemory before after {28}) :
    SolvedBuffer P fee penalty upper after := by
  apply represented.preserve {28} memory
  · intro offset inside
    simp only [Finset.mem_singleton]
    cases upper <;> simp only [multiplierSlot,Bool.false_eq_true,ite_false,ite_true] <;> omega
  · intro offset inside
    simp only [Finset.mem_singleton]
    cases upper <;> simp only [statisticsSlot,Bool.false_eq_true,ite_false,ite_true] <;> omega
  · intro offset inside
    simp only [Finset.mem_singleton]
    cases upper <;> simp only [tableLengthSlot,Bool.false_eq_true,ite_false,ite_true] <;> omega
  · intro offset _inside
    simp only [Finset.mem_singleton]
    cases upper <;> simp only [retainedTableBase,Bool.false_eq_true,ite_false,ite_true] <;> omega

/-- Counter28 is distinct from every source tag/statistic/length and both
actual retained tables. No disjointness between unrelated workspaces is used. -/
theorem representation_counter {P : Parameters} {fee : ℚ} {before after : State} {search : MultiplierState}
    (represented : SearchStateRep P fee before search) (memory : RegionMemory before after {28}) :
    SearchStateRep P fee after search := by
  have tag {cells : List Cell} (stored : HeapList before 13 cells) (length : cells.length=1) :
      HeapList after 13 cells:=by
    apply memory.heapList stored
    intro offset inside
    rw [length] at inside
    simp only [Finset.mem_singleton]
    omega
  cases search with
  | exact solution =>
    exact ⟨represented.1,tag represented.2.1 rfl,solvedBuffer_counter represented.2.2 memory⟩
  | bracket lower upper =>
    exact ⟨represented.1,represented.2.1,tag represented.2.2.1 rfl,
      solvedBuffer_counter represented.2.2.2.1 memory,solvedBuffer_counter represented.2.2.2.2 memory⟩

theorem decrement_ready {P : Parameters} {fee : ℚ} {before : State}
    (ready : Ready P fee before) (remaining : ℕ) : Ready P fee (decrementResult before remaining) := by
  have memory:=decrement_region before remaining
  refine ⟨?_,?_,?_,?_⟩
  · intro slot inside
    refine ⟨Finset.mem_insert_of_mem ((ready.header slot inside).1),?_⟩
    simp only [Nat.zero_add]
  · simpa only [decrementResult,Function.update_of_ne (by decide : (.fresh : Register)≠.index),
      Function.update_of_ne (by decide : (.fresh : Register)≠.flag),
      Function.update_of_ne (by decide : (.fresh : Register)≠.address)] using ready.fresh
  · apply memory.heapList ready.prepared
    intro offset inside
    change offset<13 at inside
    simp only [Finset.mem_singleton]
    omega
  · apply memory.heapList ready.cache
    intro offset _inside
    simp only [Finset.mem_singleton]
    omega

theorem ready_jump {P : Parameters} {fee : ℚ} {before : State}
    (ready : Ready P fee before) (target : ℕ) : Ready P fee (jumpResult before target) :=
  ⟨ready.header,ready.fresh,ready.prepared,ready.cache⟩

theorem join_entries_le (labels : RoutineLabels) (first later : List State) (middle : State)
    (last : first.getLast?=some middle) :
    PaperProofs.Paid.Computation.entryCount labels.solveEntry (joinTrace first later)≤
      PaperProofs.Paid.Computation.entryCount labels.solveEntry first+
        PaperProofs.Paid.Computation.entryCount labels.solveEntry later := by
  have split:=List.dropLast_append_getLast? middle (by rw [last];simp)
  have count : PaperProofs.Paid.Computation.entryCount labels.solveEntry first=
      PaperProofs.Paid.Computation.entryCount labels.solveEntry first.dropLast+
        PaperProofs.Paid.Computation.entryCount labels.solveEntry [middle] := by
    conv_lhs=>rw [←split]
    exact solveEntries_append labels _ _
  change PaperProofs.Paid.Computation.entryCount labels.solveEntry (first.dropLast++later)≤_
  rw [solveEntries_append]
  omega

end PDCompute.CoreSearchLoop
