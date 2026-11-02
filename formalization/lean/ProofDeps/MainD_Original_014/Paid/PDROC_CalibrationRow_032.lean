module

public import Paid.PDROC_CalibrationRow_031

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

def rightStoreResult (P : Parameters) (before : State) (base level clock cursor write : ℕ)
    (inside : cursor<2*level+1) : State :=
  let target := (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).val
  let previous := rowLeftPrefix P level clock cursor inside
  let amount := (P.walkRow level true clock).getD cursor 0*(1/2+P.certificate.gamma)
  scatterStoreResult before base write target (previous.getD target 0) amount

/-- The original right store reads the row AFTER the left store. The
post-array is prefix(cursor+1), while physical header7 remains cursor
until the separate scatterNext instructions actually store its successor. -/
theorem rightStore_correct (input : List Cell) (P : Parameters)
    (base level clock cursor read write : ℕ) (inside : cursor<2*level+1) (before : State)
    (data : ScatterLeftData P base level clock cursor read write inside before)
    (levelBound : level≤P.certificate.M+1)
    (index : before.register .index=.natural (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).val)
    (value : before.register .value=.rational ((P.walkRow level true clock).getD cursor 0*(1/2+P.certificate.gamma))) :
    linearExecute input (basicBlock .rightStore).body before=some (rightStoreResult P before base level clock cursor write inside) ∧
      ScatterBothData P base level clock cursor read write (rightStoreResult P before base level clock cursor write inside) := by
  let target := (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).val
  let previous := rowLeftPrefix P level clock cursor inside
  let amount := (P.walkRow level true clock).getD cursor 0*(1/2+P.certificate.gamma)
  have targetInRow : target<previous.size := by
    simpa only [previous,rowLeftPrefix,PDROC.endpointArrayBump_size,rowScatterPrefix_size] using
      (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).isLt
  have targetBound : target<rowWidth P.certificate.M :=
    (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).isLt.trans_le (activeWidth_le _ _ levelBound)
  have rowSize : (P.walkRow level true clock).size≤rowWidth P.certificate.M := by
    rw [PDROC.endpointWalkRow_size]
    exact activeWidth_le _ _ levelBound
  constructor
  · rw [rightStore_body]
    exact scatterStore_execute input before base write target (previous.getD target 0) amount data.control.header.fresh
      (data.control.header.live 10 (by decide)) data.control.write index value
      (data.writeRow.live target targetInRow) (data.writeRow.value target targetInRow)
  · refine ⟨RowControl.afterScatterStore P base level clock cursor read write target before
      (previous.getD target 0) amount data.control targetBound,
      scatterStore_preserves_read before base _ read write target (previous.getD target 0) amount
        (P.walkRow level true clock) data.readRow data.control.buffers targetBound rowSize,?_⟩
    rw [rowScatterPrefix_succ P level (P.walkRow level true clock) cursor inside]
    exact scatterStore_bump before base write target previous amount data.writeRow targetInRow

end PDROC.CalibrationRow
