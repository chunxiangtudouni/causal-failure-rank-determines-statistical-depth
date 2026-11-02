module

public import Paid.RootD27Core_HeapArguments_013
public import Paid.RootD27Core_EmitLoop_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

def endpointHeapOutputCode (origin base cache returnPC : ℕ) : List Instruction :=
  endpointHeapArgumentsCode base cache (origin+256)++
    (RootD27.Endpoint.endpointCode (origin+13)++emitHeapCode (origin+256) returnPC)

theorem endpointHeapOutput_length (origin base cache returnPC : ℕ) :
    (endpointHeapOutputCode origin base cache returnPC).length=263 := by
  simp only [endpointHeapOutputCode,List.length_append,endpointHeapArguments_length,
    RootD27.Endpoint.endpointCode_length,emitHeapCode]
  rfl

theorem endpoint_heap_codec_length (P : Parameters) :
    (encodeList encodeEndpoint P.endpointCache.toList).length=2*P.certificate.M+3 := by
  rw [←RootD27.Endpoint.endpointPrefix_original,RootD27.Endpoint.endpointPrefix_length]
  omega

theorem endpoint_heap_output_budget (m : ℕ) :
    7210*(m+1)+(135*(2*m+3)+30)≤7700*(m+1) := by omega

/-- The real raw-input continuation reads its prepared cells from the
live heap, computes the endpoint cache, and physically appends its original
encoding to output. It preserves all thirteen prepared cells and the
original readonly input, for literal caller code and any original input. -/
theorem endpoint_heap_output_actual (P : Parameters) (fee : ℚ)
    (input : List Cell) (program : Program) (before : State)
    (base cache returnPC : ℕ)
    (prepared : HeapList before 0 (preparedInput P fee))
    (below : 13≤base) (separated : base+48≤cache)
    (fetched : FetchesCode program before.pc
      (endpointHeapOutputCode before.pc base cache returnPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤7700*(P.certificate.M+1) ∧ after.pc=returnPC ∧
      HeapList after cache (encodeList encodeEndpoint P.endpointCache.toList) ∧
      HeapList after 0 (preparedInput P fee) ∧
      after.output=before.output++encodeList encodeEndpoint P.endpointCache.toList := by
  have setup := fetched.append_left
  have rest := fetched.append_right
  have callee := rest.append_left
  have emitter := rest.append_right
  simp only [endpointHeapArguments_length,RootD27.Endpoint.endpointCode_length,
    Nat.add_assoc] at callee emitter
  obtain ⟨computed,middle,ch,cl,cc,ct,pc,_,_,address,index,stored,retained,output⟩ :=
    endpoint_from_prepared_heap_actual P fee input program before base cache (before.pc+256)
      prepared below separated setup callee
  have count : middle.register .index=.natural (encodeList encodeEndpoint P.endpointCache.toList).length := by
    rw [endpoint_heap_codec_length]
    exact index
  obtain ⟨emitted,after,eh,el,ec,et,finalPC,_,_,heap,live,finalOutput,_⟩ :=
    emitHeap_actual program input (before.pc+256) returnPC emitter
      (encodeList encodeEndpoint P.endpointCache.toList) middle cache pc address count stored
  have emitCost : time program emitted≤135*(2*P.certificate.M+3)+30 := by
    simpa only [endpoint_heap_codec_length] using et
  have joined := joinTrace_spec program input computed emitted before middle after
    (7210*(P.certificate.M+1)) (135*(2*P.certificate.M+3)+30) ch cl eh el cc ec ct emitCost
  refine ⟨joinTrace computed emitted,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2.trans (endpoint_heap_output_budget P.certificate.M),finalPC,?_,?_,?_⟩
  · simpa only [HeapList,heapSegment,heap,live] using stored
  · simpa only [HeapList,heapSegment,heap,live] using retained
  · simpa only [output] using finalOutput

end RootD27.Core
