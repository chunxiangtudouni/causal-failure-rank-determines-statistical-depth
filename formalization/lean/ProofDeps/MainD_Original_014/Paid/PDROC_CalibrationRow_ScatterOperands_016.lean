module

public import Paid.PDROC_CalibrationRow_ScatterOperands_012
public import Paid.PDROC_CalibrationRow_ScatterOperands_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDLower.CalibrationCompute

theorem leftRead_prefix_catalog (input : List Cell) (P : Parameters)
    (base level clock cursor read write count : ℕ) (before after : State)
    (data : ScatterData P base level clock cursor read write before)
    (inside : cursor < 2 * level + 1) (levelBound : level ≤ P.certificate.M + 1)
    (index : before.register .index = .natural cursor) (bound : count ≤ 18)
    (executed : linearExecute input ((basicBlock .leftRead).body.take count) before = some after) :
    Sources before after (Catalog P base level clock) := by
  have rowInside : cursor < (P.walkRow level true clock).size := by
    simpa only [PDROC.endpointWalkRow_size] using inside
  have physicalInside : cursor < rowWidth P.certificate.M := inside.trans_le (activeWidth_le _ _ levelBound)
  change linearExecute input ((letterReadCode 12).take count) before = some after at executed
  exact letterRead_prefix_sources input before after base read cursor (2 * level + 1) 12 count
    ((P.walkRow level true clock).getD cursor 0) (1 / 2 - P.certificate.gamma) (Catalog P base level clock)
    data.control.header.fresh (data.control.header.live 9 (by decide)) data.control.read
    (data.control.header.live 12 (by decide)) data.control.header.leftBias
    (data.control.header.live 8 (by decide)) data.control.width index
    (data.readRow.live cursor rowInside) (data.readRow.value cursor rowInside)
    (offset_catalog P base level clock 9 (by decide)) (header_address_catalog P base level clock 9 (by decide))
    (read_pointer_catalog P base level clock read write data.control.buffers)
    (read_address_catalog P base level clock read write cursor data.control.buffers physicalInside)
    (Catalog.read ⟨cursor, inside⟩)
    (offset_catalog P base level clock 12 (by decide)) (header_address_catalog P base level clock 12 (by decide))
    (Catalog.channel (0 : Fin 2)) (Catalog.product ⟨cursor, inside⟩ (0 : Fin 2))
    (offset_catalog P base level clock 8 (by decide)) (header_address_catalog P base level clock 8 (by decide))
    (width_naturals_catalog P base level clock levelBound) bound executed

end PDROC.CalibrationRow.ScatterOperands
