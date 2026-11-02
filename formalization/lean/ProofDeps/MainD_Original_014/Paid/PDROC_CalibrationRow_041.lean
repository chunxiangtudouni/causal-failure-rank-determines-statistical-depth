module

public import Paid.PDROC_CalibrationRow_040

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Only the END of the real twenty-op swap has the next stable pair.
The fixed old destination row becomes the new physical read row. -/
theorem StepData.afterSwap (input : List Cell) (P : Parameters) (base level clock : ℕ) (before : State)
    (control : RowControl P base level clock (2*level+1)
      (rowPointers base P.certificate.M clock).1 (rowPointers base P.certificate.M clock).2 before)
    (newRow : RowAt before (rowPointers base P.certificate.M clock).2 (P.walkRow level true (clock+1))) :
    StepData P base level (clock+1) (stepNextResult before base clock) := by
  let read := (rowPointers base P.certificate.M clock).1
  let write := (rowPointers base P.certificate.M clock).2
  have fields := stepNext_fields before base clock read write control.read control.write
  have slots := stepNext_slots before base clock read write control.read control.write
  have body := stepNext_execute input before base clock control.header.fresh
    (control.header.live 6 (by decide)) control.clockValue
    (control.header.live 9 (by decide)) (control.header.live 10 (by decide))
  have frames := stepNext_prefix_frames (region base P.certificate.M) input before base clock control.header.fresh
    (control.header.live 6 (by decide)) control.clockValue
    (control.header.live 9 (by decide)) (control.header.live 10 (by decide))
    (header_mem_region base _ 6 (by decide) (by decide))
    (header_mem_region base _ 9 (by decide) (by decide))
    (header_mem_region base _ 10 (by decide) (by decide))
  have header := Header.transport P base level before _ control.header (frames.final body)
    (by rw [fields.2.1]; exact fun _ h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)))
    fields.2.2.1
  have updated : RowControl P base level (clock+1) (2*level+1) write read (stepNextResult before base clock) := by
    refine ⟨header,Buffers.swap base P.certificate.M read write control.buffers,
      slots.1,slots.2.1.trans control.cursorValue,?_,slots.2.2.1,slots.2.2.2⟩
    rw [fields.1,Function.update_of_ne (by omega : base+8≠base+10),
      Function.update_of_ne (by omega : base+8≠base+9),Function.update_of_ne (by omega : base+8≠base+6)]
    exact control.width
  have writeLower : base+16≤write := by
    change base+16≤(rowPointers base P.certificate.M clock).2
    rcases control.buffers with ⟨_,same⟩|⟨_,same⟩
    · rw [same]
      simp only [secondRow,rowWidth]
      omega
    · rw [same]
      simp only [firstRow]
      omega
  have row := stepNext_preserves_row before base clock read write write control.read control.write
    (P.walkRow level true (clock+1)) newRow writeLower
  constructor
  · simpa only [rowPointers_succ] using updated
  · simpa only [rowPointers_succ] using row

end PDROC.CalibrationRow
