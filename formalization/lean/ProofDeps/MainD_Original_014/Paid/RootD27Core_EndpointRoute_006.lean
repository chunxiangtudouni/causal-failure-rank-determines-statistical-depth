module

public import Paid.RootD27Core_EndpointCall_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

/-- One literal input-independent core prefix: nine genuine argument
reads followed by the243-opcode endpoint callee. The continuation starts
at252 and is actually fetched on the returned state. -/
def endpointPrefixProgram (continuation : List Instruction) : Program :=
  (endpointArgumentsCode 48 96 252++RootD27.Endpoint.endpointCode 9++continuation).toArray

theorem arrayLiteral_fetch (code : List Instruction) : FetchesCode code.toArray 0 code := by
  intro offset _
  simp only [Nat.zero_add,List.getElem?_toArray]

theorem endpointPrefix_fetch (continuation : List Instruction) :
    FetchesCode (endpointPrefixProgram continuation) 0 (endpointArgumentsCode 48 96 252) ∧
    FetchesCode (endpointPrefixProgram continuation) 9 (RootD27.Endpoint.endpointCode 9) := by
  have whole:=arrayLiteral_fetch (endpointArgumentsCode 48 96 252++(RootD27.Endpoint.endpointCode 9++continuation))
  have layout : endpointArgumentsCode 48 96 252++RootD27.Endpoint.endpointCode 9++continuation=
      endpointArgumentsCode 48 96 252++(RootD27.Endpoint.endpointCode 9++continuation) := by
    simp only [List.append_assoc]
  constructor
  · simpa only [endpointPrefixProgram,layout] using whole.append_left
  · simpa only [endpointPrefixProgram,layout,endpointArguments_length,Nat.zero_add] using whole.append_right.append_left

/-- This full original-input endpoint phase has no caller ABI or
program-fetch premises: its actual fixed literal code produces both.
The arbitrary real continuation is retained for core integration. -/
theorem original_input_endpoint_prefix (continuation : List Instruction) (P : Parameters) (fee : ℚ) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some initial ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step (endpointPrefixProgram continuation) (preparedInput P fee) first=some later) ∧
      time (endpointPrefixProgram continuation) trace≤7150*(P.certificate.M+1) ∧ after.pc=252 ∧
      after.register .fresh=.natural 48 ∧ after.register .old=.natural 252 ∧
      after.register .address=.natural 96 ∧ after.register .index=.natural (2*P.certificate.M+3) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output=[] := by
  have fetched:=endpointPrefix_fetch continuation
  exact endpoint_from_prepared_actual P fee (endpointPrefixProgram continuation) initial 48 96 252
    (by decide) fetched.1 fetched.2

end RootD27.Core
