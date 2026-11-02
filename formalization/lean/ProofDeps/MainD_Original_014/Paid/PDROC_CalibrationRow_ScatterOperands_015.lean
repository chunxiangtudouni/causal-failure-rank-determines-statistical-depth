module

public import Paid.PDROC_CalibrationRow_ScatterOperands_004
public import Paid.PDROC_CalibrationRow_ScatterOperands_005
public import Paid.PDROC_CalibrationRow_ScatterOperands_007
public import Paid.PDROC_CalibrationRow_ScatterOperands_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid.Computation PDLower.CalibrationCompute

/-- The original eighteen-op letter read is composed from the actual
row fetch, actual header probability product and actual boundary test. -/
theorem letterRead_prefix_sources (input : List Cell) (before after : State)
    (base read cursor width biasOffset count : ℕ) (mass probability : ℚ) (New : Cell → Prop)
    (fresh : before.register .fresh = .natural base)
    (readLive : base + 9 ∈ before.live) (readValue : before.heap (base + 9) = .natural read)
    (biasLive : base + biasOffset ∈ before.live) (biasValue : before.heap (base + biasOffset) = .rational probability)
    (widthLive : base + 8 ∈ before.live) (widthValue : before.heap (base + 8) = .natural width)
    (index : before.register .index = .natural cursor)
    (cellLive : read + cursor ∈ before.live) (cellValue : before.heap (read + cursor) = .rational mass)
    (readOffsetSource : New (.natural 9)) (readAddressSource : New (.natural (base + 9)))
    (pointerSource : New (.natural read)) (rowAddressSource : New (.natural (read + cursor)))
    (massSource : New (.rational mass))
    (biasOffsetSource : New (.natural biasOffset)) (biasAddressSource : New (.natural (base + biasOffset)))
    (probabilitySource : New (.rational probability)) (productSource : New (.rational (mass * probability)))
    (widthOffsetSource : New (.natural 8)) (widthAddressSource : New (.natural (base + 8)))
    (naturals : ∀ number ≤ max width 2, New (.natural number)) (bound : count ≤ 18)
    (executed : linearExecute input ((letterReadCode biasOffset).take count) before = some after) :
    Sources before after New := by
  let source := sourceReadResult before base read cursor mass
  let product := channelProductResult source base biasOffset mass probability
  have sourceFields := sourceRead_fields before base read cursor mass
  have sourceRun : linearExecute input sourceReadCode before = some source :=
    sourceRead_execute input before base read cursor mass fresh readLive readValue index cellLive cellValue
  have sourcePrefixes : ∀ n ≤ sourceReadCode.length, ∀ state,
      linearExecute input (sourceReadCode.take n) before = some state → Sources before state New := by
    intro n size state run
    exact sourceRead_prefix_sources input before state base read cursor n mass New fresh readLive readValue index
      cellLive cellValue readOffsetSource readAddressSource pointerSource rowAddressSource massSource size run
  have productRun : linearExecute input (channelProductCode biasOffset) source = some product :=
    channelProduct_execute input source base biasOffset mass probability (sourceFields.2.2.1.trans fresh)
      (by rw [sourceFields.2.1]; exact biasLive) (by rw [sourceFields.1]; exact biasValue)
      sourceFields.2.2.2.2.1
  have productPrefixes : ∀ n ≤ (channelProductCode biasOffset).length, ∀ state,
      linearExecute input ((channelProductCode biasOffset).take n) source = some state → Sources source state New := by
    intro n size state run
    exact channelProduct_prefix_sources input source state base biasOffset n mass probability New
      (sourceFields.2.2.1.trans fresh) (by rw [sourceFields.2.1]; exact biasLive)
      (by rw [sourceFields.1]; exact biasValue) sourceFields.2.2.2.2.1
      biasOffsetSource biasAddressSource probabilitySource productSource size run
  have combinedRun : linearExecute input (sourceReadCode ++ channelProductCode biasOffset) before = some product := by
    rw [linearExecute_append, sourceRun, Option.bind_some, productRun]
  have combinedPrefixes : ∀ n ≤ (sourceReadCode ++ channelProductCode biasOffset).length, ∀ state,
      linearExecute input ((sourceReadCode ++ channelProductCode biasOffset).take n) before = some state → Sources before state New := by
    intro n size state run
    exact append_prefix_sources input sourceReadCode (channelProductCode biasOffset) before source state New n
      sourceRun sourcePrefixes productPrefixes size run
  have productFields := channelProduct_fields source base biasOffset mass probability
  have productHeap : product.heap = before.heap := productFields.1.trans sourceFields.1
  have productLive : product.live = before.live := productFields.2.1.trans sourceFields.2.1
  have productFresh : product.register .fresh = .natural base := productFields.2.2.1.trans (sourceFields.2.2.1.trans fresh)
  have productIndex : product.register .index = .natural cursor := productFields.2.2.2.1.trans (sourceFields.2.2.2.1.trans index)
  have boundaryPrefixes : ∀ n ≤ boundaryCode.length, ∀ state,
      linearExecute input (boundaryCode.take n) product = some state → Sources product state New := by
    intro n size state run
    exact boundary_prefix_sources input product state base cursor width n New productFresh
      (by rw [productLive]; exact widthLive) (by rw [productHeap]; exact widthValue) productIndex
      widthOffsetSource widthAddressSource naturals size run
  exact append_prefix_sources input (sourceReadCode ++ channelProductCode biasOffset) boundaryCode
    before product after New count combinedRun combinedPrefixes boundaryPrefixes bound executed

end PDROC.CalibrationRow.ScatterOperands
