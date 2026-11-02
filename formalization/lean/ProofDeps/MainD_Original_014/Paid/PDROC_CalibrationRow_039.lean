module

public import Paid.PDROC_CalibrationRow_030
public import Paid.PDROC_CalibrationRow_034
public import Paid.PDROC_CalibrationRow_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem RowControl.afterConstantCursor (P : Parameters) (base level clock cursor read write next : ℕ)
    (before : State) (data : RowControl P base level clock cursor read write before) :
    RowControl P base level clock next read write (constantSlotResult before base 7 (.natural next)) := by
  have heap := constantSlot_heap before base 7 (.natural next)
  have live := constantSlot_live before base 7 (.natural next)
  have header := Header.transport P base level before _ data.header
    (constant_row_frame before base P.certificate.M 7 (.natural next) (by decide) (by decide))
    (by rw [live]; exact Finset.subset_insert _ _) (constantSlot_fresh before base 7 (.natural next))
  refine ⟨header,data.buffers,?_,?_,?_,?_,?_⟩
  · rw [heap,Function.update_of_ne (by omega : base+6≠base+7)]; exact data.clockValue
  · rw [heap]; simp
  · rw [heap,Function.update_of_ne (by omega : base+8≠base+7)]; exact data.width
  · rw [heap,Function.update_of_ne (by omega : base+9≠base+7)]; exact data.read
  · rw [heap,Function.update_of_ne (by omega : base+10≠base+7)]; exact data.write

theorem constantHeader_preserves_row (before : State) (base offset rowBase : ℕ) (value : Cell)
    (row : Array ℚ) (represented : RowAt before rowBase row)
    (headerOffset : offset<16) (rowLower : base+16≤rowBase) :
    RowAt (constantSlotResult before base offset value) rowBase row := by
  constructor
  · intro i inside
    rw [constantSlot_live]
    exact Finset.mem_insert_of_mem (represented.live i inside)
  · intro i inside
    rw [constantSlot_heap,Function.update_of_ne (by omega : rowBase+i≠base+offset)]
    exact represented.value i inside

/-- Stable Q-gate invariant. It is deliberately NOT asserted inside
stepNext's partial pointer swap; its exact pair is restored at block end. -/
structure StepData (P : Parameters) (base level clock : ℕ) (state : State) : Prop where
  control : RowControl P base level clock (2*level+1)
    (rowPointers base P.certificate.M clock).1 (rowPointers base P.certificate.M clock).2 state
  readRow : RowAt state (rowPointers base P.certificate.M clock).1 (P.walkRow level true clock)

theorem StepData.sameMemory (P : Parameters) (base level clock : ℕ) (before after : State)
    (data : StepData P base level clock before) (heap : after.heap=before.heap)
    (live : after.live=before.live) (fresh : after.register .fresh=before.register .fresh) :
    StepData P base level clock after := by
  have memory : MemoryFrame ∅ before after := ⟨fun _ _ => congrFun heap _,fun _ _ => by rw [live]⟩
  exact ⟨RowControl.sameMemory P base level clock (2*level+1) _ _ before after data.control heap live fresh,
    empty_frame_row before after _ _ data.readRow memory⟩

/-- The clock type is produced by the REAL store6, even when incoming
heap6 was an arbitrary Cell throughout the original initialization loop. -/
theorem StepData.start (P : Parameters) (base level : ℕ) (before : State)
    (header : Header P base level before)
    (cursor : before.heap (base+7)=.natural (2*level+1))
    (width : before.heap (base+8)=.natural (2*level+1))
    (readValue : before.heap (base+9)=.natural (firstRow base))
    (writeValue : before.heap (base+10)=.natural (secondRow base P.certificate.M))
    (readRow : RowAt before (firstRow base) (P.walkRow level true 0)) :
    StepData P base level 0 (constantSlotResult before base 6 (.natural 0)) := by
  have heap := constantSlot_heap before base 6 (.natural 0)
  have live := constantSlot_live before base 6 (.natural 0)
  have newHeader := Header.transport P base level before _ header
    (constant_row_frame before base P.certificate.M 6 (.natural 0) (by decide) (by decide))
    (by rw [live]; exact Finset.subset_insert _ _) (constantSlot_fresh before base 6 (.natural 0))
  have control : RowControl P base level 0 (2*level+1) (firstRow base) (secondRow base P.certificate.M)
      (constantSlotResult before base 6 (.natural 0)) := by
    refine ⟨newHeader,Or.inl ⟨rfl,rfl⟩,?_,?_,?_,?_,?_⟩
    · rw [heap]; simp
    · rw [heap,Function.update_of_ne (by omega : base+7≠base+6)]; exact cursor
    · rw [heap,Function.update_of_ne (by omega : base+8≠base+6)]; exact width
    · rw [heap,Function.update_of_ne (by omega : base+9≠base+6)]; exact readValue
    · rw [heap,Function.update_of_ne (by omega : base+10≠base+6)]; exact writeValue
  exact ⟨control,constantHeader_preserves_row before base 6 (firstRow base) (.natural 0)
    (P.walkRow level true 0) readRow (by decide) (by unfold firstRow; omega)⟩

end PDROC.CalibrationRow
