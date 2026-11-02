module

public import Paid.RootD27Core_Arguments_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

theorem endpoint_from_prepared_budget (m : ℕ) : 150+7000*(m+1)≤7150*(m+1) := by omega

/-- The actual core prefix reads its genuine preparedInput, constructs
the endpoint callee's six arguments, and computes the original whole
endpoint cache before returning. No prefilled header, answer cache or
successful callee run is an input hypothesis. -/
theorem endpoint_from_prepared_actual (P : Parameters) (fee : ℚ) (program : Program)
    (before : State) (base cache returnPC : ℕ) (separated : base+48≤cache)
    (setup : FetchesCode program before.pc (endpointArgumentsCode base cache returnPC))
    (callee : FetchesCode program (before.pc+9) (RootD27.Endpoint.endpointCode (before.pc+9))) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program (preparedInput P fee) first=some later) ∧
      time program trace≤7150*(P.certificate.M+1) ∧ after.pc=returnPC ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural cache ∧ after.register .index=.natural (2*P.certificate.M+3) ∧
      HeapList after cache (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output=before.output := by
  let middle:=endpointArgumentsResult P before base cache returnPC
  obtain ⟨setupTrace,sh,sl,sc,st,_⟩:=linearExecute_trace_time program (preparedInput P fee)
    (endpointArgumentsCode base cache returnPC) (endpointArguments_straight base cache returnPC)
    before middle setup (endpointArguments_execute P fee before base cache returnPC)
  have setupTime : time program setupTrace≤150 := st
  obtain ⟨actualTrace,after,ah,al,ac,actualTime,pc,fresh,old,address,index,stored,output⟩:=
    RootD27.Endpoint.endpoint_callee_actual P program (preparedInput P fee) (before.pc+9)
      middle base cache returnPC rfl rfl rfl rfl rfl rfl rfl separated callee
  have joined:=joinTrace_spec program (preparedInput P fee) setupTrace actualTrace before middle after
    150 (7000*(P.certificate.M+1)) sh sl ah al sc ac setupTime actualTime
  exact ⟨joinTrace setupTrace actualTrace,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2.trans (endpoint_from_prepared_budget P.certificate.M),pc,fresh,old,address,index,stored,output⟩

end RootD27.Core
