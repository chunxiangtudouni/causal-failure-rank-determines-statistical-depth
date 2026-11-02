module

public import Paid.PDROC_CalibrationRow_ScatterOperands_002
public import Paid.PDROC_CalibrationRow_ScatterOperands_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid.Computation PDLower.CalibrationCompute

/-- All five physical source-read prefixes retain caller cells or the
actual loaded pointer, row address and row mass. The local premises are
later obtained from the canonical ScatterEntry's Header and RowAt. -/
theorem sourceRead_prefix_sources (input : List Cell) (before after : State)
    (base read cursor count : ℕ) (mass : ℚ) (New : Cell → Prop)
    (fresh : before.register .fresh = .natural base)
    (pointerLive : base + 9 ∈ before.live) (pointer : before.heap (base + 9) = .natural read)
    (index : before.register .index = .natural cursor)
    (rowLive : read + cursor ∈ before.live) (rowValue : before.heap (read + cursor) = .rational mass)
    (offsetSource : New (.natural 9)) (slotAddressSource : New (.natural (base + 9)))
    (pointerSource : New (.natural read)) (rowAddressSource : New (.natural (read + cursor)))
    (massSource : New (.rational mass)) (bound : count ≤ 5)
    (executed : linearExecute input (sourceReadCode.take count) before = some after) :
    Sources before after New := by
  let loaded := loadSlotResult before base 9 .old
  let addressed := ({loaded with pc := loaded.pc + 1}).set .address (.natural (read + cursor))
  have loadedSource : Sources before loaded New := loadSlotResult_sources before base 9 .old New
    slotAddressSource (by rw [pointer]; exact pointerSource)
  have addressedSource : Sources before addressed New := loadedSource.trans
    ((Sources.set loaded New .address _ rowAddressSource).withPC (loaded.pc + 1))
  have finalSource : Sources before (sourceReadResult before base read cursor mass) New := by
    exact addressedSource.trans
      ((Sources.set addressed New .value _ massSource).withPC (addressed.pc + 1))
  by_cases short : count ≤ 3
  · have shortLength : count ≤ (loadSlot 9 .old).length := short
    rw [sourceReadCode, List.take_append_of_le_length shortLength] at executed
    exact loadSlot_prefix_sources input before after base 9 count .old New fresh pointerLive
      offsetSource slotAddressSource (by rw [pointer]; exact pointerSource) short executed
  · have loadRun : linearExecute input (loadSlot 9 .old) before = some loaded :=
      loadSlot_execute input before base 9 .old fresh pointerLive
    have old : loaded.register .old = .natural read := by
      simp only [loaded, loadSlotResult, Function.update_self, pointer]
    have currentIndex : loaded.register .index = .natural cursor := by
      simpa only [loaded, loadSlotResult, Function.update_of_ne (by decide : (.index : Register) ≠ .old),
        Function.update_of_ne (by decide : (.index : Register) ≠ .address)] using index
    have addressedRun : linearExecute input (sourceReadCode.take 4) before = some addressed := by
      change linearExecute input (loadSlot 9 .old ++ [.natOp .add .address .old .index]) before = some addressed
      rw [linearExecute_append, loadRun, Option.bind_some]
      have addRun : (Instruction.natOp .add .address .old .index).execute input loaded = some addressed :=
        PDMenu.ComputeFrame.execute_natOp .add .address .old .index input loaded read cursor (read + cursor)
          old currentIndex rfl
      simp only [linearExecute, addRun, Option.bind_some]
    by_cases four : count = 4
    · subst count
      have same := Option.some.inj (addressedRun.symm.trans executed)
      subst after
      exact addressedSource
    · have five : count = 5 := by omega
      subst count
      change linearExecute input sourceReadCode before = some after at executed
      rw [sourceRead_execute input before base read cursor mass fresh pointerLive pointer index rowLive rowValue] at executed
      have same := Option.some.inj executed
      subst after
      exact finalSource

end PDROC.CalibrationRow.ScatterOperands
