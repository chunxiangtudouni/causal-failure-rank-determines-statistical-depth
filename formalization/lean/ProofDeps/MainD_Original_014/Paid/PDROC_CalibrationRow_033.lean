module

public import Paid.PDROC_CalibrationRow_032
public import Paid.PDROC_CalibrationRow_024
public import Paid.PDROC_CalibrationRow_Init_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem RowControl.afterCursorIncrement (P : Parameters) (base level clock cursor read write : ℕ)
    (before : State) (data : RowControl P base level clock cursor read write before) :
    RowControl P base level clock (cursor+1) read write (incrementSlotResult before base 7 cursor) := by
  have heap : (incrementSlotResult before base 7 cursor).heap=
      Function.update before.heap (base+7) (.natural (cursor+1)) := by
    simp [incrementSlotResult,incrementSlotLoaded,storeSlotResult,loadSlotResult]
  have live : (incrementSlotResult before base 7 cursor).live=insert (base+7) before.live := rfl
  have frame := frame_of_one_update (region base P.certificate.M) before _ (base+7) (.natural (cursor+1))
    (header_mem_region base _ 7 (by decide) (by decide)) heap live
  have header := Header.transport P base level before _ data.header frame
    (by rw [live]; exact Finset.subset_insert _ _) (incrementSlot_fresh before base 7 cursor)
  refine ⟨header,data.buffers,?_,?_,?_,?_,?_⟩
  · rw [heap,Function.update_of_ne (by omega : base+6≠base+7)]; exact data.clockValue
  · rw [heap]; simp
  · rw [heap,Function.update_of_ne (by omega : base+8≠base+7)]; exact data.width
  · rw [heap,Function.update_of_ne (by omega : base+9≠base+7)]; exact data.read
  · rw [heap,Function.update_of_ne (by omega : base+10≠base+7)]; exact data.write

theorem cursorIncrement_preserves_row (before : State) (base cursor rowBase : ℕ)
    (row : Array ℚ) (represented : RowAt before rowBase row) (lower : base+16≤rowBase) :
    RowAt (incrementSlotResult before base 7 cursor) rowBase row := by
  constructor
  · intro i inside
    exact Finset.mem_insert_of_mem (represented.live i inside)
  · intro i inside
    change (Function.update before.heap (base+7) (.natural (cursor+1))) (rowBase+i)=_
    rw [Function.update_of_ne (by omega : rowBase+i≠base+7)]
    exact represented.value i inside

theorem scatterNext_body : (basicBlock Label.scatterNext).body=incrementSlot 7 := rfl

/-- This is where physical cursor REALLY becomes cursor+1. The already
stored two-letter prefix is kept in the same fixed destination buffer. -/
theorem scatterNext_correct (input : List Cell) (P : Parameters)
    (base level clock cursor read write : ℕ) (before : State)
    (data : ScatterBothData P base level clock cursor read write before) :
    linearExecute input (basicBlock .scatterNext).body before=some (incrementSlotResult before base 7 cursor) ∧
      ScatterData P base level clock (cursor+1) read write (incrementSlotResult before base 7 cursor) := by
  have readLower : base+16≤read := by
    rcases data.control.buffers with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp only [firstRow,secondRow,rowWidth] <;> omega
  have writeLower : base+16≤write := by
    rcases data.control.buffers with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp only [firstRow,secondRow,rowWidth] <;> omega
  constructor
  · rw [scatterNext_body]
    exact incrementSlot_execute input before base 7 cursor data.control.header.fresh
      (data.control.header.live 7 (by decide)) data.control.cursorValue
  · exact ⟨RowControl.afterCursorIncrement P base level clock cursor read write before data.control,
      cursorIncrement_preserves_row before base cursor read _ data.readRow readLower,
      cursorIncrement_preserves_row before base cursor write _ data.writeRow writeLower⟩

end PDROC.CalibrationRow
