module

public import Paid.PDROC_CalibrationRow_016

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- The real zero-loop invariant only asserts the written prefix of
the destination row. Its unvisited suffix can contain arbitrary old
caller data and is never read by the zero loop. -/
structure ZeroData (P : Parameters) (base level clock cursor read write : ℕ)
    (previous : Array ℚ) (state : State) : Prop where
  header : Header P base level state
  buffers : Buffers base P.certificate.M read write
  clockValue : state.heap (base+6)=.natural clock
  cursorValue : state.heap (base+7)=.natural cursor
  width : state.heap (base+8)=.natural (2*level+1)
  readValue : state.heap (base+9)=.natural read
  writeValue : state.heap (base+10)=.natural write
  previousSize : previous.size=2*level+1
  readRow : RowAt state read previous
  zeroPrefix : RowPrefix state write (Array.replicate (2*level+1) (0 : ℚ)) cursor

theorem ZeroData.sameMemory (P : Parameters) (base level clock cursor read write : ℕ)
    (previous : Array ℚ) (before after : State)
    (data : ZeroData P base level clock cursor read write previous before)
    (heap : after.heap=before.heap) (live : after.live=before.live)
    (fresh : after.register .fresh=before.register .fresh) :
    ZeroData P base level clock cursor read write previous after := by
  have header := Header.transport P base level before after data.header
    ⟨fun _ _ => congrFun heap _,fun _ _ => by rw [live]⟩ (by rw [live]) fresh
  refine ⟨header,data.buffers,?_,?_,?_,?_,?_,data.previousSize,?_,?_⟩
  · rw [heap]; exact data.clockValue
  · rw [heap]; exact data.cursorValue
  · rw [heap]; exact data.width
  · rw [heap]; exact data.readValue
  · rw [heap]; exact data.writeValue
  · exact ⟨fun i inside => by rw [live]; exact data.readRow.live i inside,
      fun i inside => by rw [heap]; exact data.readRow.value i inside⟩
  · exact ⟨data.zeroPrefix.bound,fun i inside => by rw [live]; exact data.zeroPrefix.live i inside,
      fun i inside => by rw [heap]; exact data.zeroPrefix.value i inside⟩

theorem ZeroData.advance (input : List Cell) (P : Parameters) (base level clock cursor read write : ℕ)
    (previous : Array ℚ) (before : State)
    (data : ZeroData P base level clock cursor read write previous before)
    (inside : cursor<2*level+1) (levelBound : level≤P.certificate.M+1)
    (index : before.register .index=.natural cursor) :
    ZeroData P base level clock (cursor+1) read write previous (zeroCellResult before base write cursor) := by
  have widthBound : cursor<rowWidth P.certificate.M := inside.trans_le (activeWidth_le _ _ levelBound)
  have fields := zeroCell_fields before base write cursor
  have header := Header.transport P base level before _ data.header
    (zeroCell_frame input P before base level read write cursor data.header data.buffers data.writeValue data.cursorValue index widthBound)
    (by rw [fields.2.1]; exact fun _ h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)) fields.2.2.1
  have headerNe (offset : ℕ) (bound : offset<16) : base+offset≠write+cursor :=
    Ne.symm (Buffers.write_header_ne base _ read write cursor offset data.buffers bound)
  have prefixNext := RowPrefix.writeNext before write (Array.replicate (2*level+1) (0 : ℚ)) cursor data.zeroPrefix
    (by simpa only [Array.size_replicate] using inside)
  have zeroNext : RowPrefix (writeCell before (write+cursor) (.rational 0)) write
      (Array.replicate (2*level+1) (0 : ℚ)) (cursor+1) := by
    have atCursor : (Array.replicate (2*level+1) (0 : ℚ)).getD cursor 0=0 := by
      rw [Array.getD_eq_getD_getElem?]
      simp [inside]
    simpa only [atCursor] using prefixNext
  refine ⟨header,data.buffers,?_,?_,?_,?_,?_,data.previousSize,?_,?_⟩
  · rw [fields.1,Function.update_of_ne (by omega : base+6≠base+7),Function.update_of_ne (headerNe 6 (by decide))]
    exact data.clockValue
  · rw [fields.1]; simp
  · rw [fields.1,Function.update_of_ne (by omega : base+8≠base+7),Function.update_of_ne (headerNe 8 (by decide))]
    exact data.width
  · rw [fields.1,Function.update_of_ne (by omega : base+9≠base+7),Function.update_of_ne (headerNe 9 (by decide))]
    exact data.readValue
  · rw [fields.1,Function.update_of_ne (by omega : base+10≠base+7),Function.update_of_ne (headerNe 10 (by decide))]
    exact data.writeValue
  · exact zeroCell_preserves_read before base _ read write cursor previous data.readRow data.buffers widthBound
      (data.previousSize.trans_le (activeWidth_le _ _ levelBound))
  · apply RowPrefix.transport (writeCell before (write+cursor) (.rational 0)) (zeroCellResult before base write cursor)
      write (Array.replicate (2*level+1) (0 : ℚ)) (cursor+1) zeroNext
    · rw [fields.2.1]
      exact Finset.subset_insert _ _
    · intro i _
      have separate : write+i≠base+7 := Buffers.write_header_ne base _ read write i 7 data.buffers (by decide)
      rw [fields.1,Function.update_of_ne separate]
      rfl

end PDROC.CalibrationRow
