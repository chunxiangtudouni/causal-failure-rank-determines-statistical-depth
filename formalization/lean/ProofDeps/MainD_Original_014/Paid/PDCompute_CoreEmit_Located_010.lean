module

public import Paid.PDCompute_CoreEmit_State_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.CoreEmit
open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame

def locatedProgram (origin returnPC : ℕ) : Program:=locatedBlock origin (stateCode origin returnPC).toArray

theorem located_fetch (origin returnPC : ℕ) : FetchesCode (locatedProgram origin returnPC) origin (stateCode origin returnPC) := by
  intro offset _
  simp only [locatedProgram,locatedBlock_fetch,List.getElem?_toArray]

/-- Actual original68-op state output plus genuine proper-prefix PC scope,
without assuming a whole-trace scope certificate or a free EOF. -/
theorem state_trace_located (input : List Cell) (origin returnPC : ℕ) (before : State) (n k M : ℕ) (state : MultiplierState)
    (position : before.pc=origin) (dimensions : PreparedDimensions before n k M)
    (payload : StatePayload before n k M state) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step (locatedProgram origin returnPC) input first=some later) ∧
      time (locatedProgram origin returnPC) trace≤1000*((encodeState state).length+1) ∧ after.pc=returnPC ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output++encodeState state ∧
      (∀ current∈trace,RootD27.Core.EmittedPrefix before (encodeState state) current) ∧
      peakCells trace≤workingCells before+(encodeState state).length ∧
      ∀ current∈trace.dropLast,origin≤current.pc ∧ current.pc<origin+68 := by
  obtain ⟨trace,after,head,last,chain,cost,pc,heap,live,output,prefixes,space⟩:=
    state_trace (locatedProgram origin returnPC) input origin returnPC before n k M state position dimensions payload (located_fetch origin returnPC)
  have scope : ∀ current∈trace.dropLast,origin≤current.pc ∧ current.pc<origin+68 := by
    simpa only [List.size_toArray,state_length] using
      PDLower.CalibrationCompute.located_chain_scope origin (stateCode origin returnPC).toArray input trace chain
  exact ⟨trace,after,head,last,chain,cost,pc,heap,live,output,prefixes,space,scope⟩

end PDCompute.CoreEmit
