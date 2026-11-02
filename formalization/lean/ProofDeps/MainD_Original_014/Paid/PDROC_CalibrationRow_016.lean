module

public import Paid.PDROC_CalibrationRow_015
public import Paid.PDROC_CalibrationRow_Init_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

def zeroCellResult (before : State) (base write cursor : ℕ) : State :=
  incrementSlotResult (zeroWriteResult before base write cursor) base 7 cursor

theorem zeroCell_execute (input : List Cell) (P : Parameters) (before : State)
    (base level read write cursor : ℕ) (header : Header P base level before)
    (buffers : Buffers base P.certificate.M read write)
    (pointer : before.heap (base+10)=.natural write)
    (cursorValue : before.heap (base+7)=.natural cursor)
    (index : before.register .index=.natural cursor) :
    linearExecute input (basicBlock .zeroCell).body before=some (zeroCellResult before base write cursor) := by
  rw [zeroCell_decompose,linearExecute_append,
    zeroWrite_execute input before base write cursor header.fresh (header.live 10 (by decide)) pointer index,
    Option.bind_some]
  have fields := zeroWrite_fields before base write cursor
  apply incrementSlot_execute input _ base 7 cursor (fields.2.2.1.trans header.fresh)
  · rw [fields.2.1]
    exact Finset.mem_insert_of_mem (header.live 7 (by decide))
  · rw [fields.1,Function.update_of_ne (Ne.symm
      (Buffers.write_header_ne base P.certificate.M read write cursor 7 buffers (by decide)))]
    exact cursorValue

theorem zeroCell_fields (before : State) (base write cursor : ℕ) :
    (zeroCellResult before base write cursor).heap=
      Function.update (Function.update before.heap (write+cursor) (.rational 0))
        (base+7) (.natural (cursor+1)) ∧
    (zeroCellResult before base write cursor).live=insert (base+7) (insert (write+cursor) before.live) ∧
    (zeroCellResult before base write cursor).register .fresh=before.register .fresh ∧
    (zeroCellResult before base write cursor).register .index=.natural (cursor+1) ∧
    (zeroCellResult before base write cursor).pc=before.pc+14 ∧
    (zeroCellResult before base write cursor).output=before.output := by
  simp [zeroCellResult,incrementSlotResult,incrementSlotLoaded,storeSlotResult,loadSlotResult,
    (zeroWrite_fields before base write cursor).1,(zeroWrite_fields before base write cursor).2.1,
    (zeroWrite_fields before base write cursor).2.2.1,(zeroWrite_fields before base write cursor).2.2.2.2.1,
    (zeroWrite_fields before base write cursor).2.2.2.2.2,Nat.add_assoc]

theorem zeroCell_prefix_frames (input : List Cell) (P : Parameters) (before : State)
    (base level read write cursor : ℕ) (header : Header P base level before)
    (buffers : Buffers base P.certificate.M read write)
    (pointer : before.heap (base+10)=.natural write)
    (cursorValue : before.heap (base+7)=.natural cursor)
    (index : before.register .index=.natural cursor) (inside : cursor<rowWidth P.certificate.M) :
    LinearFrames (region base P.certificate.M) input (basicBlock .zeroCell).body before := by
  rw [zeroCell_decompose]
  have lead := zeroWrite_execute input before base write cursor header.fresh (header.live 10 (by decide)) pointer index
  apply LinearFrames.append _ input zeroWriteCode (incrementSlot 7) before (zeroWriteResult before base write cursor)
    lead (zeroWrite_prefix_frames _ input before base write cursor header.fresh (header.live 10 (by decide))
      pointer index (Buffers.write_mem base P.certificate.M read write cursor buffers inside))
  have fields := zeroWrite_fields before base write cursor
  apply initIncrement_prefix_frames input _ base P.certificate.M cursor (fields.2.2.1.trans header.fresh)
  · rw [fields.2.1]
    exact Finset.mem_insert_of_mem (header.live 7 (by decide))
  · rw [fields.1,Function.update_of_ne (Ne.symm
      (Buffers.write_header_ne base P.certificate.M read write cursor 7 buffers (by decide)))]
    exact cursorValue

theorem zeroCell_frame (input : List Cell) (P : Parameters) (before : State)
    (base level read write cursor : ℕ) (header : Header P base level before)
    (buffers : Buffers base P.certificate.M read write)
    (pointer : before.heap (base+10)=.natural write)
    (cursorValue : before.heap (base+7)=.natural cursor)
    (index : before.register .index=.natural cursor) (inside : cursor<rowWidth P.certificate.M) :
    MemoryFrame (region base P.certificate.M) before (zeroCellResult before base write cursor) :=
  (zeroCell_prefix_frames input P before base level read write cursor header buffers pointer cursorValue index inside).final
    (zeroCell_execute input P before base level read write cursor header buffers pointer cursorValue index)

theorem zeroCell_preserves_read (before : State) (base M read write cursor : ℕ)
    (row : Array ℚ) (represented : RowAt before read row)
    (buffers : Buffers base M read write) (cursorBound : cursor<rowWidth M) (size : row.size≤rowWidth M) :
    RowAt (zeroCellResult before base write cursor) read row := by
  have fields := zeroCell_fields before base write cursor
  constructor
  · intro i inside
    rw [fields.2.1]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (represented.live i inside))
  · intro i inside
    have headerNe : read+i≠base+7 := by
      rcases buffers with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp only [firstRow,secondRow,rowWidth] <;> omega
    rw [fields.1,Function.update_of_ne headerNe,
      Function.update_of_ne (buffers.separate base M read write i cursor (by omega) cursorBound)]
    exact represented.value i inside

end PDROC.CalibrationRow
