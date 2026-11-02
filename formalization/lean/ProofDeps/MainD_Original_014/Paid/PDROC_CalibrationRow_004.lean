module

public import Paid.PDROC_CalibrationRow_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute

/-- A prefix of a physical row. At prefix0 this assumes no initialized
row cells at all, as required by the original levelInit entry contract. -/
structure RowPrefix (state : State) (base : ℕ) (row : Array ℚ) (count : ℕ) : Prop where
  bound : count ≤ row.size
  live : ∀ i < count,base+i ∈ state.live
  value : ∀ i < count,state.heap (base+i)=.rational (row.getD i 0)

theorem RowPrefix.zero (state : State) (base : ℕ) (row : Array ℚ) : RowPrefix state base row 0 :=
  ⟨Nat.zero_le _,fun _ inside => by omega,fun _ inside => by omega⟩

theorem RowPrefix.complete (state : State) (base : ℕ) (row : Array ℚ)
    (prefixRow : RowPrefix state base row row.size) : RowAt state base row :=
  ⟨prefixRow.live,prefixRow.value⟩

/-- Extending the actual stored prefix does not presuppose any contents
of the incoming cell or of the unvisited suffix. -/
theorem RowPrefix.writeNext (state : State) (base : ℕ) (row : Array ℚ) (count : ℕ)
    (prefixRow : RowPrefix state base row count) (inside : count < row.size) :
    RowPrefix (writeCell state (base+count) (.rational (row.getD count 0))) base row (count+1) := by
  constructor
  · omega
  · intro i beforeEnd
    by_cases same : i=count
    · subst i
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (prefixRow.live i (by omega))
  · intro i beforeEnd
    by_cases same : i=count
    · subst i
      simp [writeCell]
    · have different : base+i ≠ base+count := by omega
      simpa only [writeCell,Function.update_of_ne different] using prefixRow.value i (by omega)

theorem RowPrefix.writeOutside (state : State) (base : ℕ) (row : Array ℚ) (count address : ℕ)
    (prefixRow : RowPrefix state base row count) (stored : Cell)
    (outside : ∀ i < count,address ≠ base+i) :
    RowPrefix (writeCell state address stored) base row count := by
  constructor
  · exact prefixRow.bound
  · intro i inside
    exact Finset.mem_insert_of_mem (prefixRow.live i inside)
  · intro i inside
    simpa only [writeCell,Function.update_of_ne (Ne.symm (outside i inside))] using prefixRow.value i inside

theorem RowPrefix.transport (before after : State) (base : ℕ) (row : Array ℚ) (count : ℕ)
    (prefixRow : RowPrefix before base row count)
    (live : before.live ⊆ after.live)
    (same : ∀ i < count,after.heap (base+i)=before.heap (base+i)) : RowPrefix after base row count :=
  ⟨prefixRow.bound,fun i inside => live (prefixRow.live i inside),
    fun i inside => (same i inside).trans (prefixRow.value i inside)⟩

/-- The actual original zero-step row is delta at the physical center. -/
theorem original_center_cell (P : Parameters) (level index : ℕ) (inside : index < 2*level+1) :
    (P.walkRow level true 0).getD index 0=if index=level then 1 else 0 := by
  exact PDROC.endpointWalkDistribution_zero P level true ⟨index,inside⟩

/-- This is precisely the cell stored by initCell/initCenter/initStore. -/
theorem original_center_write (P : Parameters) (level count : ℕ) (state : State) (base : ℕ)
    (beforeEnd : count < 2*level+1)
    (prefixRow : RowPrefix state base (P.walkRow level true 0) count) :
    RowPrefix (writeCell state (base+count) (.rational (if count=level then 1 else 0)))
      base (P.walkRow level true 0) (count+1) := by
  have next := RowPrefix.writeNext state base (P.walkRow level true 0) count prefixRow
    (by simpa only [PDROC.endpointWalkRow_size] using beforeEnd)
  simpa only [original_center_cell P level count beforeEnd] using next

end PDROC.CalibrationRow
