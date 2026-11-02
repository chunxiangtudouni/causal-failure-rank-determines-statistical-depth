module

public import Paid.PDCompute_SolverScanTestMemory_064

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (loadSlot loadSlotResult storeSlot storeSlotResult)
open PDMenu.ComputeFrame

theorem scanEndpointCode_trace_memory (mode : ReaderMode) (program : Program) (input : List Cell) (P : Parameters)
    (before : State) (base source index n k : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (hindex : index ≤ P.certificate.M)
    (hpointer : values 39=.natural (source+(1+2*index)))
    (fetched : FetchesCode program before.pc (scanEndpointCode mode)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 255 ∧
      Header after base (scanEndpointValues values (P.cachedEndpoint P.endpointCache index).error
        (P.cachedEndpoint P.endpointCache index).charge) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+13 ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base := by
  let endpoint := P.cachedEndpoint P.endpointCache index
  let pointer := loadSlotResult before base 39 .address
  let address := source+(1+2*index)
  let paired := endpointPairResult pointer address endpoint.error endpoint.charge
  let first := storeSlotResult paired base 26 .total
  let after := endpointHeaderResult pointer base address endpoint.error endpoint.charge
  have fetchLoad : FetchesCode program before.pc (loadSlot 39 .address) := by
    rw [scanEndpointCode] at fetched
    exact fetched.append_left
  have fetchHeader : FetchesCode program pointer.pc (endpointHeaderCode mode) := by
    rw [scanEndpointCode] at fetched
    exact fetched.append_right
  have pointerHeader : Header pointer base values := header
  have pointerBase : pointer.register .fresh=.natural base :=
    (loadSlotResult_fresh before base 39 .address (by decide)).trans hbase
  have pointerAddress : pointer.register .address=.natural address :=
    (header.loadSlot_execute input 39 .address (by decide) hbase).2.trans hpointer
  have pointerSource : EndpointSource mode input P source pointer := by cases mode <;> exact hsource
  have errorCell : mode.HasCell input pointer address (.rational endpoint.error) :=
    EndpointSource.error mode input P source index pointer pointerSource hindex
  have chargeCell : mode.HasCell input pointer (address+1) (.rational endpoint.charge) := by
    simpa only [address,endpoint,Nat.add_assoc] using EndpointSource.charge mode input P source index pointer pointerSource hindex
  obtain ⟨loadTrace,loadHead,loadLast,loadChain,loadTime,loadMemory⟩ :=
    header.loadSlot_trace_memory program input 39 .address (by decide) hbase fetchLoad
  have fetchPair : FetchesCode program pointer.pc (endpointPairCode mode) := by
    rw [endpointHeaderCode] at fetchHeader
    exact fetchHeader.append_left.append_left
  obtain ⟨pairTrace,pairHead,pairLast,pairChain,pairTime,pairMemory⟩ :=
    linearExecute_trace_memory program input (endpointPairCode mode) (endpointPairCode_straight mode)
      pointer paired base fetchPair (endpointPairCode_execute mode input pointer address endpoint.error endpoint.charge pointerAddress errorCell chargeCell)
      (fun count bound state execute =>
        let memory := endpointPairCode_prefix_memory mode input pointer state address endpoint.error endpoint.charge
          pointerAddress errorCell chargeCell count bound execute
        HeaderMemory.of_unchanged base memory.1 memory.2.1 memory.2.2)
  have pairBound : time program pairTrace ≤ 75 := pairTime
  have pairedHeader : Header paired base values := pointerHeader
  have pairedBase : paired.register .fresh=.natural base := pointerBase
  have fetchFirst : FetchesCode program paired.pc (storeSlot 26 .total) := by
    rw [endpointHeaderCode] at fetchHeader
    exact fetchHeader.middle
  obtain ⟨firstTrace,firstHead,firstLast,firstChain,firstTime,firstMemory⟩ :=
    pairedHeader.storeSlot_trace_memory program input 26 .total (by decide) pairedBase (by decide) fetchFirst
  have firstHeader : Header first base (Function.update values 26 (.rational endpoint.error)) := by
    apply Header.update pairedHeader 26 (.rational endpoint.error)
    · simp [first,storeSlotResult,paired,endpointPairResult]
    · exact Finset.subset_insert _ _
  have firstBase : first.register .fresh=.natural base := pairedBase
  have fetchLast : FetchesCode program first.pc (storeSlot 27 .value) := by
    rw [endpointHeaderCode] at fetchHeader
    exact fetchHeader.append_right
  obtain ⟨lastTrace,lastHead,lastLast,lastChain,lastTime,lastMemory⟩ :=
    firstHeader.storeSlot_trace_memory program input 27 .value (by decide) firstBase (by decide) fetchLast
  have firstJoin := joinTrace_spec program input loadTrace pairTrace before pointer paired 60 75
    loadHead loadLast pairHead pairLast loadChain pairChain loadTime pairBound
  have firstJoinMemory := joinTrace_memory loadTrace pairTrace before pointer base loadLast loadMemory pairMemory
  have secondJoin := joinTrace_spec program input (joinTrace loadTrace pairTrace) firstTrace before paired first 135 60
    firstJoin.1 firstJoin.2.1 firstHead firstLast firstJoin.2.2.1 firstChain firstJoin.2.2.2 firstTime
  have secondJoinMemory := joinTrace_memory (joinTrace loadTrace pairTrace) firstTrace before paired base
    firstJoin.2.1 firstJoinMemory firstMemory
  have thirdJoin := joinTrace_spec program input (joinTrace (joinTrace loadTrace pairTrace) firstTrace) lastTrace before first after 195 60
    secondJoin.1 secondJoin.2.1 lastHead lastLast secondJoin.2.2.1 lastChain secondJoin.2.2.2 lastTime
  have thirdJoinMemory := joinTrace_memory (joinTrace (joinTrace loadTrace pairTrace) firstTrace) lastTrace before first base
    secondJoin.2.1 secondJoinMemory lastMemory
  refine ⟨joinTrace (joinTrace (joinTrace loadTrace pairTrace) firstTrace) lastTrace,after,
    thirdJoin.1,thirdJoin.2.1,thirdJoin.2.2.1,thirdJoin.2.2.2,
    endpointHeaderResult_header pointer base address endpoint.error endpoint.charge values pointerHeader,
    (endpointHeaderResult_fresh pointer base address endpoint.error endpoint.charge).trans pointerBase,?_,
    (loadSlotResult_frame before base 39 n k .address).trans
      (endpointHeaderResult_frame pointer base address n k endpoint.error endpoint.charge),
    (endpointHeaderResult_output pointer base address endpoint.error endpoint.charge).trans
      (loadSlotResult_output before base 39 .address),thirdJoinMemory⟩
  change (endpointHeaderResult pointer base address endpoint.error endpoint.charge).pc=before.pc+13
  rw [endpointHeaderResult_pc,loadSlotResult_pc]

end PDCompute.Solver
