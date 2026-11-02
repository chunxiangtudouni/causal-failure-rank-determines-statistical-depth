module

public import Paid.RootD27Core_RetainedSaved_053
public import Paid.RootD27Core_RetainedCaller_038

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- The SAME real retained-table copy witness in the original caller,
with proper-prefix PC scope derived from its actual successful chain.
The original readonly input and all record/functional facts are kept. -/
theorem retained_table_copy_saved_in_caller (P : Parameters) (fee penalty : ℚ)
    (program : Program) (input : List Cell) (before : State) (base returnPC : ℕ) (upper : Bool)
    (prepared : HeapList before 0 (preparedInput P fee))
    (fresh : before.register .fresh=.natural base)
    (address : before.register .address=.natural (resultBase base P.certificate.stages P.tools))
    (index : before.register .index=.natural (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length)
    (table : HeapList before (resultBase base P.certificate.stages P.tools)
      (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)))
    (fetched : FetchesCode program before.pc (retainedCopyCode before.pc upper returnPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤150*(encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length+375 ∧
      after.pc=returnPC ∧ after.register .old=.natural returnPC ∧ after.register .index=.natural 0 ∧
      HeapList after (retainedTableBase base P.certificate.stages P.tools upper)
        (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)) ∧
      HeapList after (resultBase base P.certificate.stages P.tools)
        (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)) ∧
      HeapList after 0 (preparedInput P fee) ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+
        (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length+2 ∧
      (∀ state∈trace,RegionMemory before state (retainedCopyRegion base P.certificate.stages P.tools
        (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length upper)) ∧
      (∀ state∈trace.dropLast,before.pc≤state.pc ∧ state.pc<before.pc+29) ∧
      HeapList after 46 [.natural (resultBase base P.certificate.stages P.tools),
        .natural (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length] := by
  let located:=retainedCopyLocatedProgram before.pc upper returnPC
  have literal : FetchesCode located before.pc (retainedCopyCode before.pc upper returnPC) := by
    intro offset _inside
    dsimp only [located]
    rw [retainedCopyLocatedProgram,locatedBlock_fetch,List.getElem?_toArray]
  obtain ⟨trace,after,head,last,chain,cost,pc,old,indexAfter,destination,sourceHeap,preparedAfter,output,peak,memory,saved⟩:=
    retained_table_copy_saved_actual P fee penalty located input before base returnPC upper
      prepared fresh address index table literal
  have fullScope:=PDLower.CalibrationCompute.located_chain_scope before.pc
    (retainedCopyCode before.pc upper returnPC).toArray input trace chain
  have scope : ∀ state∈trace.dropLast,before.pc≤state.pc ∧
      state.pc<before.pc+(retainedCopyCode before.pc upper returnPC).length := by
    simpa only [List.size_toArray] using fullScope
  have sameFetch : ∀ state∈trace.dropLast,located[state.pc]?=program[state.pc]? := by
    intro state member
    have bounds:=scope state member
    have addressed : before.pc+(state.pc-before.pc)=state.pc:=Nat.add_sub_of_le bounds.1
    have offsetBound : state.pc-before.pc<(retainedCopyCode before.pc upper returnPC).length:=by omega
    calc
      located[state.pc]?=located[before.pc+(state.pc-before.pc)]? := by rw [addressed]
      _=(retainedCopyCode before.pc upper returnPC)[state.pc-before.pc]? := by
        dsimp only [located]
        rw [retainedCopyLocatedProgram,locatedBlock_fetch,List.getElem?_toArray]
      _=program[before.pc+(state.pc-before.pc)]? := (fetched (state.pc-before.pc) offsetBound).symm
      _=program[state.pc]? := by rw [addressed]
  have actual:=chain_same_input_of_fetch located program input trace sameFetch chain
  have actualCost:=(time_le_of_dropLast_fetch_eq located program trace sameFetch).trans (Nat.add_le_add_right cost 15)
  refine ⟨trace,after,head,last,actual,actualCost.trans (by omega),pc,old,indexAfter,destination,sourceHeap,
    preparedAfter,output,peak,memory,?_,saved⟩
  simpa only [retainedCopy_length] using scope

end RootD27.Core
