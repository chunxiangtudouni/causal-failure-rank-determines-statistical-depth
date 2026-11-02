module

public import Paid.RootD27Core_EndpointRoute_006
public import Paid.RootD27Core_EmitLoop_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

def endpointOutputPrefixProgram (continuation : List Instruction) : Program :=
  endpointPrefixProgram (emitHeapCode 252 259++continuation)

theorem original_endpoint_codec_length (P : Parameters) :
    (encodeList encodeEndpoint P.endpointCache.toList).length=2*P.certificate.M+3 := by
  rw [←RootD27.Endpoint.endpointPrefix_original,RootD27.Endpoint.endpointPrefix_length]
  omega

theorem endpointOutput_fetch (continuation : List Instruction) :
    FetchesCode (endpointOutputPrefixProgram continuation) 252 (emitHeapCode 252 259) := by
  have whole:=arrayLiteral_fetch (endpointArgumentsCode 48 96 252++
    (RootD27.Endpoint.endpointCode 9++(emitHeapCode 252 259++continuation)))
  have fetched:=whole.append_right.append_right.append_left
  simpa only [endpointOutputPrefixProgram,endpointPrefixProgram,List.append_assoc,
    endpointArguments_length,RootD27.Endpoint.endpointCode_length,Nat.zero_add] using fetched

theorem endpoint_output_budget (m : ℕ) : 7150*(m+1)+(135*(2*m+3)+30)≤7600*(m+1) := by omega

/-- The same fixed core prefix now REALLY outputs the complete original
endpoint encoding. It reads only preparedInput, computes all endpoints,
emits the live cache by original instructions and reaches its literal
continuation at259. No cache/output certificate is a caller input. -/
theorem original_input_endpoint_output (continuation : List Instruction) (P : Parameters) (fee : ℚ) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some initial ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step (endpointOutputPrefixProgram continuation) (preparedInput P fee) first=some later) ∧
      time (endpointOutputPrefixProgram continuation) trace≤7600*(P.certificate.M+1) ∧ after.pc=259 ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      after.output=encodeList encodeEndpoint P.endpointCache.toList := by
  let program:=endpointOutputPrefixProgram continuation
  obtain ⟨computed,middle,ch,cl,cc,ct,pc,_,_,address,index,stored,output⟩:=
    original_input_endpoint_prefix (emitHeapCode 252 259++continuation) P fee
  have count : middle.register .index=.natural (encodeList encodeEndpoint P.endpointCache.toList).length := by
    rw [original_endpoint_codec_length]
    exact index
  obtain ⟨emitted,after,eh,el,ec,et,finalPC,_,_,heap,live,finalOutput,_⟩:=
    emitHeap_actual program (preparedInput P fee) 252 259 (endpointOutput_fetch continuation)
      (encodeList encodeEndpoint P.endpointCache.toList) middle 96 pc address count stored
  have emitCost : time program emitted≤135*(2*P.certificate.M+3)+30 := by
    simpa only [original_endpoint_codec_length] using et
  have joined:=joinTrace_spec program (preparedInput P fee) computed emitted initial middle after
    (7150*(P.certificate.M+1)) (135*(2*P.certificate.M+3)+30) ch cl eh el cc ec ct emitCost
  refine ⟨joinTrace computed emitted,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2.trans (endpoint_output_budget P.certificate.M),finalPC,?_,?_⟩
  · simpa only [HeapList,heapSegment,heap,live] using stored
  · simpa only [output,List.nil_append] using finalOutput

end RootD27.Core
