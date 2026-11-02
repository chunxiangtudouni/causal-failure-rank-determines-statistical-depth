module

public import Paid.PDROC_CalibrationRow_ScatterOperands_008
public import Paid.PDROC_CalibrationRow_ScatterOperands_009
public import Paid.PDROC_CalibrationRow_ScatterOperands_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDLower.CalibrationCompute

theorem leftStore_prefix_catalog (input : List Cell) (P : Parameters)
    (base level clock cursor read write count : ℕ) (before after : State)
    (data : ScatterData P base level clock cursor read write before)
    (inside : cursor < 2 * level + 1) (levelBound : level ≤ P.certificate.M + 1)
    (index : before.register .index = .natural (walkMove level ⟨cursor, inside⟩ (0 : Fin 2)).val)
    (value : before.register .value = .rational ((P.walkRow level true clock).getD cursor 0 * (1 / 2 - P.certificate.gamma)))
    (bound : count ≤ 7)
    (executed : linearExecute input (scatterStoreCode.take count) before = some after) :
    Sources before after (Catalog P base level clock) := by
  let target := walkMove level ⟨cursor, inside⟩ (0 : Fin 2)
  let previous := rowScatterPrefix P level (P.walkRow level true clock) cursor
  let amount := (P.walkRow level true clock).getD cursor 0 * (1 / 2 - P.certificate.gamma)
  have rowInside : target.val < previous.size := by
    simpa only [previous, rowScatterPrefix_size] using target.isLt
  have physicalInside : target.val < rowWidth P.certificate.M :=
    target.isLt.trans_le (activeWidth_le _ _ levelBound)
  exact scatterStore_prefix_sources input before after base write target.val count (previous.getD target.val 0) amount
    (Catalog P base level clock) data.control.header.fresh (data.control.header.live 10 (by decide))
    data.control.write index value (data.writeRow.live target.val rowInside) (data.writeRow.value target.val rowInside)
    (offset_catalog P base level clock 10 (by decide)) (header_address_catalog P base level clock 10 (by decide))
    (write_pointer_catalog P base level clock read write data.control.buffers)
    (write_address_catalog P base level clock read write target.val data.control.buffers physicalInside)
    (Catalog.partialRow cursor inside.le target)
    (leftStore_sum_catalog input P base level clock cursor read write before data inside levelBound index value) bound executed

theorem rightStore_prefix_catalog (input : List Cell) (P : Parameters)
    (base level clock cursor read write count : ℕ) (inside : cursor < 2 * level + 1) (before after : State)
    (data : ScatterLeftData P base level clock cursor read write inside before)
    (levelBound : level ≤ P.certificate.M + 1)
    (index : before.register .index = .natural (walkMove level ⟨cursor, inside⟩ (1 : Fin 2)).val)
    (value : before.register .value = .rational ((P.walkRow level true clock).getD cursor 0 * (1 / 2 + P.certificate.gamma)))
    (bound : count ≤ 7)
    (executed : linearExecute input (scatterStoreCode.take count) before = some after) :
    Sources before after (Catalog P base level clock) := by
  let target := walkMove level ⟨cursor, inside⟩ (1 : Fin 2)
  let previous := rowLeftPrefix P level clock cursor inside
  let amount := (P.walkRow level true clock).getD cursor 0 * (1 / 2 + P.certificate.gamma)
  have rowInside : target.val < previous.size := by
    simpa only [previous, rowLeftPrefix, PDROC.endpointArrayBump_size, rowScatterPrefix_size] using target.isLt
  have physicalInside : target.val < rowWidth P.certificate.M :=
    target.isLt.trans_le (activeWidth_le _ _ levelBound)
  exact scatterStore_prefix_sources input before after base write target.val count (previous.getD target.val 0) amount
    (Catalog P base level clock) data.control.header.fresh (data.control.header.live 10 (by decide))
    data.control.write index value (data.writeRow.live target.val rowInside) (data.writeRow.value target.val rowInside)
    (offset_catalog P base level clock 10 (by decide)) (header_address_catalog P base level clock 10 (by decide))
    (write_pointer_catalog P base level clock read write data.control.buffers)
    (write_address_catalog P base level clock read write target.val data.control.buffers physicalInside)
    (Catalog.afterLeft cursor inside target)
    (rightStore_sum_catalog input P base level clock cursor read write inside before data levelBound index value) bound executed

end PDROC.CalibrationRow.ScatterOperands
