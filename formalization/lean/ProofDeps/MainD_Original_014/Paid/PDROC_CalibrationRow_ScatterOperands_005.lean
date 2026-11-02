module

public import Paid.PDROC_CalibrationRow_ScatterOperands_002
public import Paid.PDROC_CalibrationRow_ScatterOperands_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid.Computation PDLower.CalibrationCompute

/-- The probability is really read from its header cell. Only the
single actual product is newly assigned; incoming unrelated registers
are retained as caller values throughout all four literal prefixes. -/
theorem channelProduct_prefix_sources (input : List Cell) (before after : State)
    (base biasOffset count : ℕ) (mass probability : ℚ) (New : Cell → Prop)
    (fresh : before.register .fresh = .natural base)
    (biasLive : base + biasOffset ∈ before.live)
    (bias : before.heap (base + biasOffset) = .rational probability)
    (value : before.register .value = .rational mass)
    (offsetSource : New (.natural biasOffset)) (addressSource : New (.natural (base + biasOffset)))
    (probabilitySource : New (.rational probability)) (productSource : New (.rational (mass * probability)))
    (bound : count ≤ 4)
    (executed : linearExecute input ((channelProductCode biasOffset).take count) before = some after) :
    Sources before after New := by
  let loaded := loadSlotResult before base biasOffset .old
  have loadedSource : Sources before loaded New := loadSlotResult_sources before base biasOffset .old New
    addressSource (by rw [bias]; exact probabilitySource)
  have finalSource : Sources before (channelProductResult before base biasOffset mass probability) New :=
    loadedSource.trans ((Sources.set loaded New .value _ productSource).withPC (loaded.pc + 1))
  by_cases short : count ≤ 3
  · have shortLength : count ≤ (loadSlot biasOffset .old).length := short
    rw [channelProductCode, List.take_append_of_le_length shortLength] at executed
    exact loadSlot_prefix_sources input before after base biasOffset count .old New fresh biasLive
      offsetSource addressSource (by rw [bias]; exact probabilitySource) short executed
  · have four : count = 4 := by omega
    subst count
    change linearExecute input (channelProductCode biasOffset) before = some after at executed
    rw [channelProduct_execute input before base biasOffset mass probability fresh biasLive bias value] at executed
    have same := Option.some.inj executed
    subst after
    exact finalSource

end PDROC.CalibrationRow.ScatterOperands
