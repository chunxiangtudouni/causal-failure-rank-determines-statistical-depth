module

public import Paid.PDCompute_SolverHeaderFrame_099

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Computation

/-- The heap really contains every completed original entry. The entry
function is a logical invariant, never program data or a machine oracle. -/
def DensePrefix (state : State) (base k : ℕ) (entry : ℕ → ℕ → MenuEntry) (done : ℕ) : Prop :=
  ∀ row column, column ≤ k → row*(k+1)+column < done →
    PDLower.CalibrationCompute.HeapList state (cellBase base k row column) (denseEncodeEntry (entry row column))

theorem DensePrefix.empty (state : State) (base k : ℕ) (entry : ℕ → ℕ → MenuEntry) :
    DensePrefix state base k entry 0 := by
  intro row column _ earlier
  omega

theorem denseIndex_injective (k row first other second : ℕ) (hfirst : first ≤ k) (hsecond : second ≤ k)
    (same : row*(k+1)+first=other*(k+1)+second) : row=other ∧ first=second := by
  have rows : row=other := by
    by_contra different
    rcases lt_or_gt_of_ne different with less|greater
    · have bound:=Nat.mul_le_mul_right (k+1) (Nat.succ_le_of_lt less)
      nlinarith
    · have bound:=Nat.mul_le_mul_right (k+1) (Nat.succ_le_of_lt greater)
      nlinarith
  exact ⟨rows,by rw [rows] at same; omega⟩

theorem earlierDenseCell_outside (base k row column oldRow oldColumn offset : ℕ)
    (earlier : oldRow*(k+1)+oldColumn < row*(k+1)+column) (bound : offset < 6) :
    cellBase base k oldRow oldColumn+offset ∉ cellRegion (cellBase base k row column) 6 := by
  rw [mem_cellRegion_iff]
  unfold cellBase tableBase headerWords entryWords
  omega

/-- An actual current-entry write preserves every older entry even when
old and new cells occupy the SAME larger caller workspace. -/
theorem DensePrefix.extend {before after : State} {base k row column : ℕ} {entry : ℕ → ℕ → MenuEntry}
    (columnBound : column ≤ k)
    (prior : DensePrefix before base k entry (row*(k+1)+column))
    (memory : RegionMemory before after (cellRegion (cellBase base k row column) 6))
    (written : PDLower.CalibrationCompute.HeapList after (cellBase base k row column) (denseEncodeEntry (entry row column))) :
    DensePrefix after base k entry (row*(k+1)+column+1) := by
  intro oldRow oldColumn oldColumnBound earlier
  by_cases old : oldRow*(k+1)+oldColumn < row*(k+1)+column
  · apply memory.heapList (prior oldRow oldColumn oldColumnBound old)
    intro offset bound
    exact earlierDenseCell_outside base k row column oldRow oldColumn offset old
      (by simpa only [denseEncodeEntry_length,entryWords] using bound)
  · have same : oldRow*(k+1)+oldColumn=row*(k+1)+column := by omega
    obtain ⟨rfl,rfl⟩:=denseIndex_injective k oldRow oldColumn row column oldColumnBound columnBound same
    exact written

theorem DensePrefix.header {before after : State} {base k done : ℕ} {entry : ℕ → ℕ → MenuEntry}
    (prior : DensePrefix before base k entry done) (memory : HeaderMemory before after base) :
    DensePrefix after base k entry done := by
  intro row column columnBound earlier
  apply memory.heapList (prior row column columnBound earlier)
  intro offset _
  right
  unfold cellBase tableBase headerWords entryWords
  omega

theorem DensePrefix.previous_row {state : State} {base k row column : ℕ} {entry : ℕ → ℕ → MenuEntry}
    (prior : DensePrefix state base k entry (row*(k+1)+column)) (positive : 0 < row) (columnBound : column ≤ k) :
    PDLower.CalibrationCompute.HeapList state (cellBase base k (row-1) column) (denseEncodeEntry (entry (row-1) column)) := by
  apply prior (row-1) column columnBound
  have rowEq : row-1+1=row := Nat.sub_add_cancel positive
  have product : (row-1)*(k+1)+(k+1)=row*(k+1) := by
    calc
      _ = (row-1+1)*(k+1) := by ring
      _ = _ := by rw [rowEq]
  omega

theorem DensePrefix.previous_tools {state : State} {base k row column : ℕ} {entry : ℕ → ℕ → MenuEntry}
    (prior : DensePrefix state base k entry (row*(k+1)+column)) (positiveRow : 0 < row)
    (positiveColumn : 0 < column) (columnBound : column ≤ k) :
    PDLower.CalibrationCompute.HeapList state (cellBase base k (row-1) (column-1))
      (denseEncodeEntry (entry (row-1) (column-1))) := by
  apply prior (row-1) (column-1) (by omega)
  have rowEq : row-1+1=row := Nat.sub_add_cancel positiveRow
  have product : (row-1)*(k+1)+(k+1)=row*(k+1) := by
    calc
      _ = (row-1+1)*(k+1) := by ring
      _ = _ := by rw [rowEq]
  omega

end PDCompute.Solver
