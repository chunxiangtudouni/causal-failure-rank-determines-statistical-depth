module

public import Paid.RootD27Core_CalibrationCaller_024
public import Paid.RootD27Core_HeapOutput_014
public import Paid.RootD27Endpoint_CalleeSpace_036
public import Paid.PDLower_CalibrationCompute_ReadOnly_051

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver

/-- The SAME real heap-argument setup, full endpoint callee and emitting
loop. All old live cells and output are counted at every intermediate
state; the original cache and thirteen prepared cells remain available. -/
theorem endpoint_heap_output_actual_space (P : Parameters) (fee : ℚ)
    (input : List Cell) (program : Program) (before : State) (base cache returnPC : ℕ)
    (prepared : HeapList before 0 (preparedInput P fee))
    (below : 13≤base) (separated : base+48≤cache)
    (fetched : FetchesCode program before.pc (endpointHeapOutputCode before.pc base cache returnPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤7700*(P.certificate.M+1) ∧ after.pc=returnPC ∧
      HeapList after cache (encodeList encodeEndpoint P.endpointCache.toList) ∧
      HeapList after 0 (preparedInput P fee) ∧
      after.output=before.output++encodeList encodeEndpoint P.endpointCache.toList ∧
      peakCells trace≤workingCells before+(4*P.certificate.M+54) ∧
      (∀ state∈trace,workingCells state≤workingCells before+(4*P.certificate.M+54)) := by
  have setupFetch:=fetched.append_left
  have bodyFetch:=fetched.append_right.append_left
  have emitFetch:=fetched.append_right.append_right
  simp only [endpointHeapArguments_length,RootD27.Endpoint.endpointCode_length,Nat.add_assoc] at bodyFetch emitFetch
  let entered:=endpointHeapArgumentsResult P before base cache (before.pc+256)
  obtain ⟨setup,sh,sl,sc,st,prefixes⟩:=linearExecute_trace_time program input
    (endpointHeapArgumentsCode base cache (before.pc+256))
    (endpointHeapArguments_straight base cache (before.pc+256)) before entered setupFetch
    (endpointHeapArguments_execute P fee input before base cache (before.pc+256) prepared)
  have setupMemory (state : State) (member : state∈setup) : workingCells state=workingCells before := by
    have split:=List.dropLast_append_getLast? entered (by rw [sl];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,_bound,actual⟩:=prefixes state proper
      have readonly : (endpointHeapArgumentsCode base cache (before.pc+256)).all PDLower.CalibrationCompute.readOnly=true:=rfl
      have takeReadonly : ((endpointHeapArgumentsCode base cache (before.pc+256)).take count).all
          PDLower.CalibrationCompute.readOnly=true := by
        apply List.all_eq_true.mpr
        intro instruction inside
        exact (List.all_eq_true.mp readonly) instruction (List.mem_of_mem_take inside)
      obtain ⟨_heap,live,output⟩:=PDLower.CalibrationCompute.linearReadOnly_heap input _ before state takeReadonly actual
      simp only [workingCells,live,output]
    · have same : state=entered:=List.mem_singleton.mp terminal
      subst state
      rfl
  obtain ⟨body,computed,bh,bl,bc,bt,pc,_fresh,_old,address,index,stored,output,frame,peak,_region⟩:=
    RootD27.Endpoint.endpoint_callee_actual_space P program input (before.pc+13) entered base cache (before.pc+256)
      rfl rfl rfl rfl rfl rfl rfl separated bodyFetch
  have computationBound (state : State) (member : state∈body) :
      workingCells state≤workingCells before+(2*P.certificate.M+51) :=
    (workingCells_le_peak_of_member body state member).trans peak
  have computedBound:=computationBound computed (List.mem_of_getLast? bl)
  have retained : HeapList computed 0 (preparedInput P fee) := by
    apply frame.heapList prepared
    intro offset inside
    change offset<13 at inside
    omega
  have count : computed.register .index=.natural (encodeList encodeEndpoint P.endpointCache.toList).length := by
    rw [endpoint_heap_codec_length]
    exact index
  obtain ⟨emitted,after,eh,el,ec,et,finalPC,_finalAddress,_finalIndex,heap,live,finalOutput,emissionPrefixes⟩:=
    emitHeap_actual program input (before.pc+256) returnPC emitFetch
      (encodeList encodeEndpoint P.endpointCache.toList) computed cache pc address count stored
  have emitCost : time program emitted≤135*(2*P.certificate.M+3)+30 := by
    simpa only [endpoint_heap_codec_length] using et
  have computedTrace:=joinTrace_spec program input setup body before entered computed
    210 (7000*(P.certificate.M+1)) sh sl bh bl sc bc st bt
  have joined:=joinTrace_spec program input (joinTrace setup body) emitted before computed after
    (7210*(P.certificate.M+1)) (135*(2*P.certificate.M+3)+30)
      computedTrace.1 computedTrace.2.1 eh el computedTrace.2.2.1 ec
      (computedTrace.2.2.2.trans (endpoint_heap_budget P.certificate.M)) emitCost
  have allBounds : ∀ state∈joinTrace (joinTrace setup body) emitted,
      workingCells state≤workingCells before+(4*P.certificate.M+54) := by
    intro state member
    rcases joinTrace_member member with first|last
    · rcases joinTrace_member first with setupMember|bodyMember
      · rw [setupMemory state setupMember]
        omega
      · have bound:=computationBound state bodyMember
        omega
    · obtain ⟨_sameHeap,sameLive,written,pending,split,emittedOutput⟩:=emissionPrefixes state last
      have length:=congrArg List.length split
      rw [List.length_append,endpoint_heap_codec_length] at length
      have cells : workingCells state=workingCells computed+written.length := by
        simp only [workingCells,sameLive,emittedOutput,List.length_append]
        omega
      rw [cells]
      omega
  refine ⟨joinTrace (joinTrace setup body) emitted,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2.trans (endpoint_heap_output_budget P.certificate.M),finalPC,?_,?_,?_,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allBounds,allBounds⟩
  · simpa only [HeapList,heapSegment,heap,live] using stored
  · simpa only [HeapList,heapSegment,heap,live] using retained
  · simpa only [output,show entered.output=before.output from rfl] using finalOutput

end RootD27.Core
