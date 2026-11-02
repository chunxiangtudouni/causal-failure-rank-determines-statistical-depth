module

public import Paid.PDROC_CalibrationRow_030

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem RowControl.afterScatterStore (P : Parameters) (base level clock cursor read write target : ℕ)
    (before : State) (previous amount : ℚ) (data : RowControl P base level clock cursor read write before)
    (inside : target<rowWidth P.certificate.M) :
    RowControl P base level clock cursor read write (scatterStoreResult before base write target previous amount) := by
  have fields := scatterStore_fields before base write target previous amount
  have frame : MemoryFrame (region base P.certificate.M) before (scatterStoreResult before base write target previous amount) :=
    frame_of_one_update _ before _ (write+target) (.rational (previous+amount))
      (Buffers.write_mem base P.certificate.M read write target data.buffers inside) fields.1 fields.2.1
  have header := Header.transport P base level before _ data.header frame
    (by rw [fields.2.1]; exact Finset.subset_insert _ _) fields.2.2.1
  have unchanged (offset : ℕ) (bound : offset<16) :
      (scatterStoreResult before base write target previous amount).heap (base+offset)=before.heap (base+offset) := by
    rw [fields.1]
    exact Function.update_of_ne (Ne.symm (Buffers.write_header_ne base _ read write target offset data.buffers bound)) _ _
  exact ⟨header,data.buffers,(unchanged 6 (by decide)).trans data.clockValue,
    (unchanged 7 (by decide)).trans data.cursorValue,(unchanged 8 (by decide)).trans data.width,
    (unchanged 9 (by decide)).trans data.read,(unchanged 10 (by decide)).trans data.write⟩

def leftStoreResult (P : Parameters) (before : State) (base level clock cursor write : ℕ)
    (inside : cursor<2*level+1) : State :=
  let target := (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val
  let previous := rowScatterPrefix P level (P.walkRow level true clock) cursor
  let amount := (P.walkRow level true clock).getD cursor 0*(1/2-P.certificate.gamma)
  scatterStoreResult before base write target (previous.getD target 0) amount

/-- The actual left store creates exactly Root's frozen rowLeftPrefix,
while header7 remains the ORIGINAL source cursor. -/
theorem leftStore_correct (input : List Cell) (P : Parameters)
    (base level clock cursor read write : ℕ) (before : State)
    (data : ScatterData P base level clock cursor read write before)
    (inside : cursor<2*level+1) (levelBound : level≤P.certificate.M+1)
    (index : before.register .index=.natural (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val)
    (value : before.register .value=.rational ((P.walkRow level true clock).getD cursor 0*(1/2-P.certificate.gamma))) :
    linearExecute input (basicBlock .leftStore).body before=some (leftStoreResult P before base level clock cursor write inside) ∧
      ScatterLeftData P base level clock cursor read write inside (leftStoreResult P before base level clock cursor write inside) := by
  let target := (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val
  let previous := rowScatterPrefix P level (P.walkRow level true clock) cursor
  let amount := (P.walkRow level true clock).getD cursor 0*(1/2-P.certificate.gamma)
  have targetInRow : target<previous.size := by
    simpa only [previous,rowScatterPrefix_size] using (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).isLt
  have targetBound : target<rowWidth P.certificate.M :=
    (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).isLt.trans_le (activeWidth_le _ _ levelBound)
  have rowSize : (P.walkRow level true clock).size≤rowWidth P.certificate.M := by
    rw [PDROC.endpointWalkRow_size]
    exact activeWidth_le _ _ levelBound
  constructor
  · rw [leftStore_body]
    exact scatterStore_execute input before base write target (previous.getD target 0) amount data.control.header.fresh
      (data.control.header.live 10 (by decide)) data.control.write index value
      (data.writeRow.live target targetInRow) (data.writeRow.value target targetInRow)
  · exact ⟨RowControl.afterScatterStore P base level clock cursor read write target before
      (previous.getD target 0) amount data.control targetBound,
      scatterStore_preserves_read before base _ read write target (previous.getD target 0) amount
        (P.walkRow level true clock) data.readRow data.control.buffers targetBound rowSize,
      scatterStore_bump before base write target previous amount data.writeRow targetInRow⟩

end PDROC.CalibrationRow
