module

public import Paid.PDROC_CalibrationRow_ScatterOperands_002
public import Paid.PDROC_CalibrationRow_ScatterOperands_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid.Computation PDLower.CalibrationCompute

/-- The loaded old partial sum and the pre-store addition result are
catalogued separately. Concrete left/right entries identify that result
with the frozen firstLeft/nextPartial value, without recurrent bits_add. -/
theorem scatterStore_prefix_sources (input : List Cell) (before after : State)
    (base rowBase target count : ℕ) (previous amount : ℚ) (New : Cell → Prop)
    (fresh : before.register .fresh = .natural base)
    (pointerLive : base + 10 ∈ before.live) (pointer : before.heap (base + 10) = .natural rowBase)
    (index : before.register .index = .natural target) (payload : before.register .value = .rational amount)
    (cellLive : rowBase + target ∈ before.live) (cellValue : before.heap (rowBase + target) = .rational previous)
    (offsetSource : New (.natural 10)) (slotAddressSource : New (.natural (base + 10)))
    (pointerSource : New (.natural rowBase)) (rowAddressSource : New (.natural (rowBase + target)))
    (previousSource : New (.rational previous)) (sumSource : New (.rational (previous + amount)))
    (bound : count ≤ 7)
    (executed : linearExecute input (scatterStoreCode.take count) before = some after) :
    Sources before after New := by
  let loaded := loadSlotResult before base 10 .old
  let addressed := ({loaded with pc := loaded.pc + 1}).set .address (.natural (rowBase + target))
  let fetched := ({addressed with pc := addressed.pc + 1}).set .old (.rational previous)
  let added := ({fetched with pc := fetched.pc + 1}).set .value (.rational (previous + amount))
  have loadedSource : Sources before loaded New := loadSlotResult_sources before base 10 .old New
    slotAddressSource (by rw [pointer]; exact pointerSource)
  have addressedSource : Sources before addressed New := loadedSource.trans
    ((Sources.set loaded New .address _ rowAddressSource).withPC (loaded.pc + 1))
  have fetchedSource : Sources before fetched New := addressedSource.trans
    ((Sources.set addressed New .old _ previousSource).withPC (addressed.pc + 1))
  have addedSource : Sources before added New := fetchedSource.trans
    ((Sources.set fetched New .value _ sumSource).withPC (fetched.pc + 1))
  have finalSource : Sources before (scatterStoreResult before base rowBase target previous amount) New :=
    addedSource.trans ((Sources.store added New (rowBase + target) _ sumSource rowAddressSource).withPC (added.pc + 1))
  by_cases short : count ≤ 3
  · have shortLength : count ≤ (loadSlot 10 .old).length := short
    rw [scatterStoreCode, List.take_append_of_le_length shortLength] at executed
    exact loadSlot_prefix_sources input before after base 10 count .old New fresh pointerLive
      offsetSource slotAddressSource (by rw [pointer]; exact pointerSource) short executed
  · have loadRun : linearExecute input (loadSlot 10 .old) before = some loaded :=
      loadSlot_execute input before base 10 .old fresh pointerLive
    have addressedRun : (Instruction.natOp .add .address .old .index).execute input loaded = some addressed := by
      simp [Instruction.execute, loaded, loadSlotResult, State.set, pointer, index, Cell.nat?, NatOp.eval, addressed]
    have fetchedRun : (Instruction.load .old .address).execute input addressed = some fetched := by
      simp [Instruction.execute, addressed, loaded, loadSlotResult, State.set, cellLive, cellValue, Cell.nat?, fetched]
    have addedRun : (Instruction.ratOp .add .value .old .value).execute input fetched = some added := by
      simp [Instruction.execute, fetched, addressed, loaded, loadSlotResult, State.set, payload, Cell.rat?, RatOp.eval, added]
    have lower : 4 ≤ count := by omega
    interval_cases count
    · have run : linearExecute input (scatterStoreCode.take 4) before = some addressed := by
        change linearExecute input (loadSlot 10 .old ++ [.natOp .add .address .old .index]) before = some addressed
        rw [linearExecute_append, loadRun, Option.bind_some]
        simp only [linearExecute, addressedRun, Option.bind_some]
      have same := Option.some.inj (run.symm.trans executed)
      subst after
      exact addressedSource
    · have run : linearExecute input (scatterStoreCode.take 5) before = some fetched := by
        change linearExecute input (loadSlot 10 .old ++ [.natOp .add .address .old .index, .load .old .address]) before = some fetched
        rw [linearExecute_append, loadRun, Option.bind_some]
        simp only [linearExecute, addressedRun, fetchedRun, Option.bind_some]
      have same := Option.some.inj (run.symm.trans executed)
      subst after
      exact fetchedSource
    · have run : linearExecute input (scatterStoreCode.take 6) before = some added := by
        change linearExecute input (loadSlot 10 .old ++
          [.natOp .add .address .old .index, .load .old .address, .ratOp .add .value .old .value]) before = some added
        rw [linearExecute_append, loadRun, Option.bind_some]
        simp only [linearExecute, addressedRun, fetchedRun, addedRun, Option.bind_some]
      have same := Option.some.inj (run.symm.trans executed)
      subst after
      exact addedSource
    · change linearExecute input scatterStoreCode before = some after at executed
      rw [scatterStore_execute input before base rowBase target previous amount fresh pointerLive pointer index payload cellLive cellValue] at executed
      have same := Option.some.inj executed
      subst after
      exact finalSource

end PDROC.CalibrationRow.ScatterOperands
