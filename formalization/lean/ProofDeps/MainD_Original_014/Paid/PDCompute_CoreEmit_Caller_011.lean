module

public import Paid.PDCompute_CoreEmit_Located_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000

@[expose] public section

namespace PDCompute.CoreEmit
open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame

/-- Complete real caller integration. The SAME physical witness retains
all output/heap/live/space/scope facts under actual fetched instructions.
Its real final-state time allowance15 is paid by a fixed linear constant. -/
theorem state_trace_in_program (program : Program) (input : List Cell) (origin returnPC : ℕ)
    (before : State) (n k M : ℕ) (state : MultiplierState)
    (position : before.pc=origin) (dimensions : PreparedDimensions before n k M)
    (payload : StatePayload before n k M state)
    (fetch : FetchesCode program origin (stateCode origin returnPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤1024*((encodeState state).length+1) ∧ after.pc=returnPC ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output++encodeState state ∧
      (∀ current∈trace,RootD27.Core.EmittedPrefix before (encodeState state) current) ∧
      peakCells trace≤workingCells before+(encodeState state).length ∧
      ∀ current∈trace.dropLast,origin≤current.pc ∧ current.pc<origin+68 := by
  obtain ⟨trace,after,head,last,chain,cost,pc,heap,live,output,prefixes,space,scope⟩:=
    state_trace_located input origin returnPC before n k M state position dimensions payload
  have fetched : ∀ current∈trace.dropLast,(locatedProgram origin returnPC)[current.pc]?=program[current.pc]? := by
    intro current member
    have bounds:=scope current member
    have addressed : origin+(current.pc-origin)=current.pc:=Nat.add_sub_of_le bounds.1
    have offsetBound : current.pc-origin<(stateCode origin returnPC).length := by rw [state_length];omega
    calc
      (locatedProgram origin returnPC)[current.pc]?=(locatedProgram origin returnPC)[origin+(current.pc-origin)]? := by rw [addressed]
      _=(stateCode origin returnPC)[current.pc-origin]? := by rw [locatedProgram,locatedBlock_fetch,List.getElem?_toArray]
      _=program[origin+(current.pc-origin)]? := (fetch (current.pc-origin) offsetBound).symm
      _=program[current.pc]? := by rw [addressed]
  have callerChain:=RootD27.Core.chain_same_input_of_fetch _ program input trace fetched chain
  have callerCost:=(time_le_of_dropLast_fetch_eq _ program trace fetched).trans (Nat.add_le_add_right cost 15)
  refine ⟨trace,after,head,last,callerChain,?_,pc,heap,live,output,prefixes,space,scope⟩
  omega

end PDCompute.CoreEmit
