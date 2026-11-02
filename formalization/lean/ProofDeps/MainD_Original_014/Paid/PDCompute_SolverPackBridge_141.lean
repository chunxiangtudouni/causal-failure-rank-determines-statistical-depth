module

public import Paid.PDCompute_SolverMatrixRuntime_130
public import Paid.PDCompute_Pack_Callee_067

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

theorem originalTable_rows (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    (P.cachedSolveMenuTable P.endpointCache fee penalty k n).size=n+1 := by
  rw [cachedSolveMenuTable_eq]
  exact P.solveMenuTable_size fee penalty k n

theorem originalTable_columns (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    ∀ row∈P.cachedSolveMenuTable P.endpointCache fee penalty k n,row.size=k+1 := by
  rw [cachedSolveMenuTable_eq]
  exact P.solveMenuTable_row_size fee penalty k n

/-- True six-cell entry facts of the original matrix, with real bounded
array indices. This does not assume any serialized answer. -/
theorem DenseOriginalTable.pack_cells {state : State} {P : Parameters} {fee penalty : ℚ} {base n k : ℕ}
    (dense : DenseOriginalTable state P fee penalty base n k) :
    ∀ (row : ℕ) (rowBound : row<(P.cachedSolveMenuTable P.endpointCache fee penalty k n).size)
      (column : ℕ) (columnBound : column<(P.cachedSolveMenuTable P.endpointCache fee penalty k n)[row].size),
      PDLower.CalibrationCompute.HeapList state (cellBase base k row column)
        (denseEncodeEntry (P.cachedSolveMenuTable P.endpointCache fee penalty k n)[row][column]) := by
  intro row rowBound column columnBound
  have rowLe : row≤n := by rw [originalTable_rows P fee penalty n k] at rowBound; omega
  have width := originalTable_columns P fee penalty n k _ (Array.getElem_mem rowBound)
  have columnLe : column≤k := by rw [width] at columnBound; omega
  have actual := dense row rowLe column columnLe
  have rowEq : (P.cachedSolveMenuTable P.endpointCache fee penalty k n).getD row #[]=
      (P.cachedSolveMenuTable P.endpointCache fee penalty k n)[row] := (Array.getElem_eq_getD #[]).symm
  have columnEq : ((P.cachedSolveMenuTable P.endpointCache fee penalty k n)[row]).getD column abandonEntry=
      (P.cachedSolveMenuTable P.endpointCache fee penalty k n)[row][column] := (Array.getElem_eq_getD abandonEntry).symm
  simpa only [menuEntryAt,rowEq,columnEq] using actual

theorem pack_writeRegion_subset_workspace (base n k : ℕ) :
    PDCompute.Pack.writeRegion base n k ⊆ workspace base n k := by
  intro address member
  rcases Finset.mem_union.mp member with header|result
  · exact headerRegion_subset_workspace base n k header
  · obtain ⟨offset,inside,rfl⟩ := Finset.mem_image.mp result
    have bound := Finset.mem_range.mp inside
    apply Finset.mem_image.mpr
    refine ⟨headerWords+entryWords*entryCount n k+offset,Finset.mem_range.mpr ?_,?_⟩
    · unfold workspaceSize
      omega
    · unfold resultBase tableBase
      omega

end PDCompute.Solver
