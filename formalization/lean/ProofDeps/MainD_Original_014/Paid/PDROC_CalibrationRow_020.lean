module

public import Paid.PDROC_CalibrationRow_018

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

def letterReadCode (biasOffset : ℕ) : List Instruction :=
  sourceReadCode++channelProductCode biasOffset++boundaryCode

def letterReadResult (before : State) (base read cursor width biasOffset : ℕ) (mass probability : ℚ) : State :=
  boundaryResult (channelProductResult (sourceReadResult before base read cursor mass)
    base biasOffset mass probability) base cursor width

/-- Actual read-row, channel multiplication and absorbing-boundary test
are proved in execution order. The runtime cursor is the original row
index until the separate one-step interior block changes its target. -/
theorem letterRead_execute (input : List Cell) (before : State)
    (base read cursor width biasOffset : ℕ) (mass probability : ℚ)
    (fresh : before.register .fresh=.natural base)
    (readLive : base+9 ∈ before.live) (readValue : before.heap (base+9)=.natural read)
    (biasLive : base+biasOffset ∈ before.live) (biasValue : before.heap (base+biasOffset)=.rational probability)
    (widthLive : base+8 ∈ before.live) (widthValue : before.heap (base+8)=.natural width)
    (index : before.register .index=.natural cursor)
    (cellLive : read+cursor ∈ before.live) (cellValue : before.heap (read+cursor)=.rational mass) :
    linearExecute input (letterReadCode biasOffset) before=
      some (letterReadResult before base read cursor width biasOffset mass probability) := by
  let source := sourceReadResult before base read cursor mass
  have sourceFields := sourceRead_fields before base read cursor mass
  have sourceLive : source.live=before.live := sourceFields.2.1
  have sourceHeap : source.heap=before.heap := sourceFields.1
  have sourceRun := sourceRead_execute input before base read cursor mass fresh readLive readValue index cellLive cellValue
  have productRun := channelProduct_execute input source base biasOffset mass probability
    (sourceFields.2.2.1.trans fresh) (by rw [sourceLive]; exact biasLive)
    (by rw [sourceHeap]; exact biasValue) sourceFields.2.2.2.2.1
  let product := channelProductResult source base biasOffset mass probability
  have productFields := channelProduct_fields source base biasOffset mass probability
  have productLive : product.live=before.live := productFields.2.1.trans sourceLive
  have productHeap : product.heap=before.heap := productFields.1.trans sourceHeap
  have boundaryRun := boundary_execute input product base cursor width
    (productFields.2.2.1.trans (sourceFields.2.2.1.trans fresh))
    (by rw [productLive]; exact widthLive)
    (by rw [productHeap]; exact widthValue)
    (productFields.2.2.2.1.trans (sourceFields.2.2.2.1.trans index))
  rw [letterReadCode,linearExecute_append,linearExecute_append,sourceRun,Option.bind_some,
    productRun,Option.bind_some,boundaryRun]
  rfl

theorem letterRead_fields (before : State) (base read cursor width biasOffset : ℕ) (mass probability : ℚ) :
    (letterReadResult before base read cursor width biasOffset mass probability).heap=before.heap ∧
    (letterReadResult before base read cursor width biasOffset mass probability).live=before.live ∧
    (letterReadResult before base read cursor width biasOffset mass probability).register .fresh=before.register .fresh ∧
    (letterReadResult before base read cursor width biasOffset mass probability).register .index=before.register .index ∧
    (letterReadResult before base read cursor width biasOffset mass probability).register .value=.rational (mass*probability) ∧
    (letterReadResult before base read cursor width biasOffset mass probability).register .flag=.natural (boundaryFlag cursor width) ∧
    (letterReadResult before base read cursor width biasOffset mass probability).pc=before.pc+18 ∧
    (letterReadResult before base read cursor width biasOffset mass probability).output=before.output := by
  simp only [letterReadResult,(boundary_fields _ _ _ _).1,(boundary_fields _ _ _ _).2.1,
    (boundary_fields _ _ _ _).2.2.1,(boundary_fields _ _ _ _).2.2.2.1,
    (boundary_fields _ _ _ _).2.2.2.2.1,(boundary_fields _ _ _ _).2.2.2.2.2.1,
    (boundary_fields _ _ _ _).2.2.2.2.2.2.1,(boundary_fields _ _ _ _).2.2.2.2.2.2.2,
    (channelProduct_fields _ _ _ _ _).1,(channelProduct_fields _ _ _ _ _).2.1,
    (channelProduct_fields _ _ _ _ _).2.2.1,(channelProduct_fields _ _ _ _ _).2.2.2.1,
    (channelProduct_fields _ _ _ _ _).2.2.2.2.1,(channelProduct_fields _ _ _ _ _).2.2.2.2.2.1,
    (channelProduct_fields _ _ _ _ _).2.2.2.2.2.2,
    (sourceRead_fields _ _ _ _ _).1,(sourceRead_fields _ _ _ _ _).2.1,
    (sourceRead_fields _ _ _ _ _).2.2.1,(sourceRead_fields _ _ _ _ _).2.2.2.1,
    (sourceRead_fields _ _ _ _ _).2.2.2.2.2.1,(sourceRead_fields _ _ _ _ _).2.2.2.2.2.2,Nat.add_assoc]
  trivial

end PDROC.CalibrationRow
