module

public import Paid.PDROC_CalibrationRow_ScatterOperands_012
public import Paid.PDROC_CalibrationRow_ScatterOperands_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDLower.CalibrationCompute

/-- The right read really reloads header7 after the left target move.
It is not given an already-restored source index at entry. -/
theorem rightRead_prefix_catalog (input : List Cell) (P : Parameters)
    (base level clock cursor read write count : ℕ) (inside : cursor < 2 * level + 1) (before after : State)
    (data : ScatterLeftData P base level clock cursor read write inside before)
    (levelBound : level ≤ P.certificate.M + 1) (bound : count ≤ 21)
    (executed : linearExecute input ((basicBlock .rightRead).body.take count) before = some after) :
    Sources before after (Catalog P base level clock) := by
  let loaded := loadSlotResult before base 7 .index
  have cursorSource : Catalog P base level clock (.natural cursor) := by
    apply small_natural_catalog
    have width := activeWidth_le P.certificate.M level levelBound
    omega
  have loadRun : linearExecute input (loadSlot 7 .index) before = some loaded :=
    loadSlot_execute input before base 7 .index data.control.header.fresh (data.control.header.live 7 (by decide))
  have loadPrefixes : ∀ n ≤ (loadSlot 7 .index).length, ∀ state,
      linearExecute input ((loadSlot 7 .index).take n) before = some state → Sources before state (Catalog P base level clock) := by
    intro n size state run
    exact loadSlot_prefix_sources input before state base 7 n .index (Catalog P base level clock)
      data.control.header.fresh (data.control.header.live 7 (by decide))
      (offset_catalog P base level clock 7 (by decide)) (header_address_catalog P base level clock 7 (by decide))
      (by rw [data.control.cursorValue]; exact cursorSource) size run
  have freshSame : loaded.register .fresh = before.register .fresh := by simp [loaded, loadSlotResult]
  have current := ScatterLeftData.sameMemory P base level clock cursor read write inside before loaded data rfl rfl freshSame
  have index : loaded.register .index = .natural cursor := by simp [loaded, loadSlotResult, data.control.cursorValue]
  have rowInside : cursor < (P.walkRow level true clock).size := by
    simpa only [PDROC.endpointWalkRow_size] using inside
  have physicalInside : cursor < rowWidth P.certificate.M := inside.trans_le (activeWidth_le _ _ levelBound)
  have laterPrefixes : ∀ n ≤ (letterReadCode 13).length, ∀ state,
      linearExecute input ((letterReadCode 13).take n) loaded = some state → Sources loaded state (Catalog P base level clock) := by
    intro n size state run
    exact letterRead_prefix_sources input loaded state base read cursor (2 * level + 1) 13 n
      ((P.walkRow level true clock).getD cursor 0) (1 / 2 + P.certificate.gamma) (Catalog P base level clock)
      current.control.header.fresh (current.control.header.live 9 (by decide)) current.control.read
      (current.control.header.live 13 (by decide)) current.control.header.rightBias
      (current.control.header.live 8 (by decide)) current.control.width index
      (current.readRow.live cursor rowInside) (current.readRow.value cursor rowInside)
      (offset_catalog P base level clock 9 (by decide)) (header_address_catalog P base level clock 9 (by decide))
      (read_pointer_catalog P base level clock read write current.control.buffers)
      (read_address_catalog P base level clock read write cursor current.control.buffers physicalInside)
      (Catalog.read ⟨cursor, inside⟩)
      (offset_catalog P base level clock 13 (by decide)) (header_address_catalog P base level clock 13 (by decide))
      (Catalog.channel (1 : Fin 2)) (Catalog.product ⟨cursor, inside⟩ (1 : Fin 2))
      (offset_catalog P base level clock 8 (by decide)) (header_address_catalog P base level clock 8 (by decide))
      (width_naturals_catalog P base level clock levelBound) size run
  change linearExecute input ((loadSlot 7 .index ++ letterReadCode 13).take count) before = some after at executed
  exact append_prefix_sources input (loadSlot 7 .index) (letterReadCode 13) before loaded after
    (Catalog P base level clock) count loadRun loadPrefixes laterPrefixes bound executed

end PDROC.CalibrationRow.ScatterOperands
