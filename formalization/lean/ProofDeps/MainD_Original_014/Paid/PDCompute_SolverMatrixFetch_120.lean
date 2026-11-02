module

public import Paid.PDCompute_SolverMatrixProgram_113

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000
set_option maxRecDepth 2048

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

attribute [local irreducible] fullCellCode

def matrixRowTestPC (origin : ℕ) : ℕ := origin+(headerCode [.constant 19 (.natural 0)]).length
def matrixColumnInitPC (origin : ℕ) : ℕ := matrixRowTestPC origin+8
def matrixColumnTestPC (origin : ℕ) : ℕ := matrixColumnInitPC origin+(headerCode [.constant 20 (.natural 0)]).length
def matrixCellPC (origin : ℕ) : ℕ := matrixColumnTestPC origin+8
def matrixColumnBackPC (mode : ReaderMode) (origin : ℕ) : ℕ :=
  matrixCellPC origin+(fullCellCode mode (matrixCellPC origin)).length+(addNatSlot 20 1).length
def matrixRowAdvancePC (mode : ReaderMode) (origin : ℕ) : ℕ := matrixColumnBackPC mode origin+1
def matrixRowBackPC (mode : ReaderMode) (origin : ℕ) : ℕ := matrixRowAdvancePC mode origin+(addNatSlot 19 1).length
def matrixEndPC (mode : ReaderMode) (origin : ℕ) : ℕ := matrixRowBackPC mode origin+1

theorem naturalBranchCode_length (comparison : Comparison) (left right a b : ℕ) :
    (naturalBranchCode comparison left right a b).length=8 := rfl

theorem matrix_row_init_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (matrixCode mode origin)) :
    FetchesCode program origin (headerCode [.constant 19 (.natural 0)]) :=
  fetch.append_left.append_left.append_left.append_left.append_left.append_left.append_left.append_left

theorem matrix_row_test_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (matrixCode mode origin)) :
    FetchesCode program (matrixRowTestPC origin)
      (naturalBranchCode .lessEqual 19 3 (matrixEndPC mode origin) (matrixColumnInitPC origin)) :=
  fetch.append_left.append_left.append_left.append_left.append_left.append_left.append_left.append_right

theorem matrix_column_init_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (matrixCode mode origin)) :
    FetchesCode program (matrixColumnInitPC origin) (headerCode [.constant 20 (.natural 0)]) := by
  have body:=fetch.append_left.append_left.append_left.append_left.append_left.append_left.append_right
  simpa only [List.length_append,naturalBranchCode_length,matrixColumnInitPC,matrixRowTestPC,Nat.add_assoc] using body

theorem matrix_column_test_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (matrixCode mode origin)) :
    FetchesCode program (matrixColumnTestPC origin)
      (naturalBranchCode .lessEqual 20 4 (matrixRowAdvancePC mode origin) (matrixCellPC origin)) := by
  have body:=fetch.append_left.append_left.append_left.append_left.append_left.append_right
  simpa only [List.length_append,naturalBranchCode_length,matrixRowAdvancePC,matrixColumnBackPC,matrixCellPC,
    matrixColumnTestPC,matrixColumnInitPC,matrixRowTestPC,Nat.add_assoc] using body

theorem matrix_cell_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (matrixCode mode origin)) :
    FetchesCode program (matrixCellPC origin) (fullCellCode mode (matrixCellPC origin)) := by
  have body:=fetch.append_left.append_left.append_left.append_left.append_right
  simpa only [List.length_append,naturalBranchCode_length,matrixCellPC,matrixColumnTestPC,matrixColumnInitPC,matrixRowTestPC,Nat.add_assoc] using body

theorem matrix_column_advance_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (matrixCode mode origin)) :
    FetchesCode program (matrixCellPC origin+(fullCellCode mode (matrixCellPC origin)).length) (addNatSlot 20 1) := by
  have body:=fetch.append_left.append_left.append_left.append_right
  simpa only [List.length_append,naturalBranchCode_length,matrixCellPC,matrixColumnTestPC,matrixColumnInitPC,matrixRowTestPC,Nat.add_assoc] using body

theorem matrix_column_back_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (matrixCode mode origin)) :
    program[matrixColumnBackPC mode origin]?=some (.jump (matrixColumnTestPC origin)) := by
  have body:=fetch.append_left.append_left.append_right
  have instruction:=body 0 (by change 0 < 1; decide)
  simpa only [List.length_append,naturalBranchCode_length,matrixColumnBackPC,matrixCellPC,matrixColumnTestPC,
    matrixColumnInitPC,matrixRowTestPC,Nat.add_zero,Nat.add_assoc,List.getElem?_cons_zero] using instruction

theorem matrix_row_advance_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (matrixCode mode origin)) :
    FetchesCode program (matrixRowAdvancePC mode origin) (addNatSlot 19 1) := by
  have body:=fetch.append_left.append_right
  simpa only [List.length_append,List.length_singleton,naturalBranchCode_length,matrixRowAdvancePC,matrixColumnBackPC,
    matrixCellPC,matrixColumnTestPC,matrixColumnInitPC,matrixRowTestPC,Nat.add_assoc] using body

theorem matrix_row_back_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (matrixCode mode origin)) :
    program[matrixRowBackPC mode origin]?=some (.jump (matrixRowTestPC origin)) := by
  have instruction:=fetch.append_right 0 (by change 0 < 1; decide)
  simpa only [List.length_append,List.length_singleton,naturalBranchCode_length,matrixRowBackPC,matrixRowAdvancePC,matrixColumnBackPC,
    matrixCellPC,matrixColumnTestPC,matrixColumnInitPC,matrixRowTestPC,Nat.add_zero,Nat.add_assoc,List.getElem?_cons_zero] using instruction

theorem matrixCode_end (mode : ReaderMode) (origin : ℕ) : origin+(matrixCode mode origin).length=matrixEndPC mode origin := by
  simp only [matrixCode,List.length_append,List.length_singleton,naturalBranchCode_length,matrixEndPC,matrixRowBackPC,
    matrixRowAdvancePC,matrixColumnBackPC,matrixCellPC,matrixColumnTestPC,matrixColumnInitPC,matrixRowTestPC]
  omega

end PDCompute.Solver
