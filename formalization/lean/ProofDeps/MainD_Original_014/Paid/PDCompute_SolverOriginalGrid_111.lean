module

public import Paid.PDCompute_SolverDensePrefix_109
public import PaperProofs.Paid.PDMenu_MenuStoredRecursion_079

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

/-- Logical ORIGINAL rows and cells, independent of any final truncation.
They are proof invariants; no such function is added to the machine. -/
def solverRow (P : Parameters) (fee penalty : ℚ) (k row : ℕ) : MenuRow :=
  (P.cachedSolveMenuTable P.endpointCache fee penalty k row).getD row #[]

def solverEntry (P : Parameters) (fee penalty : ℚ) (k row column : ℕ) : MenuEntry :=
  (solverRow P fee penalty k row).getD column abandonEntry

theorem solverEntry_zero (P : Parameters) (fee penalty : ℚ) (k column : ℕ) (bound : column ≤ k) :
    solverEntry P fee penalty k 0 column=finishEntry := by
  change (baseMenuRow k).getD column abandonEntry=finishEntry
  exact PDMenu.baseMenuRow_getD k column bound

theorem solverEntry_succ (P : Parameters) (fee penalty : ℚ) (k row column : ℕ) (bound : column ≤ k) :
    solverEntry P fee penalty k (row+1) column=
      P.cachedNextMenuEntry P.endpointCache fee penalty (solverRow P fee penalty k row) column := by
  simpa only [solverEntry,solverRow,cachedSolveMenuTable_eq,cachedNextMenuEntry_eq,menuEntryAt] using
    PDMenu.solveMenuTable_last_entry_succ P fee penalty k row column bound

theorem solverEntry_in_full (P : Parameters) (fee penalty : ℚ) (n k row column : ℕ) (bound : row ≤ n) :
    menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty k n) row column=
      solverEntry P fee penalty k row column := by
  simpa only [solverEntry,solverRow,cachedSolveMenuTable_eq,menuEntryAt] using
    PDMenu.solveMenuTable_cell_prefix P fee penalty k n row bound column

/-- Actual dense heap for exactly the complete original table. -/
def DenseOriginalTable (state : State) (P : Parameters) (fee penalty : ℚ) (base n k : ℕ) : Prop :=
  ∀ row ≤ n, ∀ column ≤ k,
    PDLower.CalibrationCompute.HeapList state (cellBase base k row column)
      (denseEncodeEntry (menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty k n) row column))

theorem DensePrefix.original_table (state : State) (P : Parameters) (fee penalty : ℚ) (base n k : ℕ)
    (complete : DensePrefix state base k (solverEntry P fee penalty k) (entryCount n k)) :
    DenseOriginalTable state P fee penalty base n k := by
  intro row rowBound column columnBound
  rw [solverEntry_in_full P fee penalty n k row column rowBound]
  apply complete row column columnBound
  have rowProduct:=Nat.mul_le_mul_right (k+1) rowBound
  unfold entryCount
  nlinarith

end PDCompute.Solver
