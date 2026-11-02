module
public import Paid.PDCompute_CorePrelude_EndpointCallee_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
@[expose] public section
namespace PDCompute.CorePrelude
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDCompute.CoreSearchBudget PDCompute.Solver PDMenu.ComputeFrame RootD27.Core RootD27.Bits
open PDROC.CalibrationRow.Operand
open PDLower.CalibrationCompute (linearExecute)

/-- Complete real setup13/callee243/output7, retaining the SAME numeric
trace and counting entry52 once after actual shared-head deduplication. -/
theorem endpoint_output_counted (P : Parameters) (fee : ℚ) (program : Program) (input : List Cell)
    (before : State) (position : before.pc=39) (prepared : HeapList before 0 (preparedInput P fee))
    (safe : SafeBits before (inputBudget P fee))
    (fetch : FetchesCode program 39 (endpointHeapOutputCode 39 48 96 302)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤8000*(P.certificate.M+1) ∧ after.pc=302 ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      after.output=before.output++encodeList encodeEndpoint P.endpointCache.toList ∧
      peakCells trace≤workingCells before+4*P.certificate.M+54 ∧
      (∀ state∈trace,SafeBits state (endpointBudget P fee)) ∧
      (∀ state∈trace,39≤state.pc ∧ state.pc≤302) ∧
      (∀ state∈trace.dropLast,state.pc<302) ∧
      PaperProofs.Paid.Computation.entryCount 52 trace=1 := by
  let entered:=endpointHeapArgumentsResult P before 48 96 295
  have positive:=coreOperandBound_positive P fee
  have small : 64≤ inputBudget P fee:=by unfold inputBudget;omega
  have natural (n : ℕ) (bound : n≤512) : (Cell.natural n).bits≤ inputBudget P fee:=
    (Nat.add_le_add_left (natBits_mono bound) 1).trans ((by decide : 1+natBits 512≤64).trans small)
  have setupFetch : FetchesCode program before.pc (endpointHeapArgumentsCode 48 96 295):=by
    rw [position]
    exact fetch.append_left
  have setupSafe:=PDROC.CoreOperands.endpoint_heap_arguments_prefix_safe input before 48 96 295 (inputBudget P fee)
    safe (fun slot inside=>by simpa only [Nat.zero_add] using prepared.1 slot inside) (by omega)
    (natural 48 (by decide)) (natural 96 (by decide)) (natural 295 (by decide))
    (by rw [position];exact ((by decide : natBits (39+13)≤64).trans small))
  obtain ⟨setup,sh,sl,sc,st,setupResources,setupScope,setupProper⟩:=readonly_linear_resources program input
    (endpointHeapArgumentsCode 48 96 295) before entered (inputBudget P fee)
    (endpointHeapArguments_straight _ _ _) setupFetch
    (endpointHeapArguments_execute P fee input before 48 96 295 prepared) setupSafe
    (fun count bound state actual=>endpoint_arguments_memory P fee input before state 48 96 295 count prepared bound actual)
  have entrySafe:=setupSafe.final (endpointHeapArguments_execute P fee input before 48 96 295 prepared)
  have entryPC : entered.pc=52:=by change before.pc+13=52;omega
  have bounds:=PDROC.EndpointOperands.operandBudget_of_caller P 52 48 96 295 (inputBudget P fee) entered entrySafe
    entryPC rfl rfl rfl rfl
  let localProgram:=locatedBlock 52 (RootD27.Endpoint.endpointCode 52).toArray
  have localFetch : FetchesCode localProgram 52 (RootD27.Endpoint.endpointCode 52):=by
    intro offset inside
    rw [locatedBlock_fetch,List.getElem?_toArray]
  obtain ⟨callee,computed,ch,cl,cc,ct,computedPC,computedFresh,computedOld,computedAddress,computedIndex,cache,
    computedOutput,frame,calleePeak,calleeResources,calleeCount,_calleeClosed,_calleeProper⟩:=
    endpoint_callee_counted P localProgram input 52 entered 48 96 (endpointBudget P fee)
      entryPC rfl rfl rfl rfl rfl rfl (by decide) localFetch bounds.2.2 bounds.1 bounds.2.1
  have calleeFetch : FetchesCode program 52 (RootD27.Endpoint.endpointCode 52):=by
    simpa only [endpointHeapArguments_length] using fetch.append_right.append_left
  have embedded:=located_trace_in_program program input 52 (RootD27.Endpoint.endpointCode 52) callee calleeFetch cc
  have calleeScope : ∀ state∈callee,52≤state.pc ∧ state.pc≤295:=by
    intro state member
    have split:=List.dropLast_append_getLast? computed (by rw [cl];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · have scope:=embedded.2.2 state proper
      rw [RootD27.Endpoint.endpointCode_length] at scope
      omega
    · have same:=List.mem_singleton.mp terminal
      subst state
      omega
  have preparedComputed : HeapList computed 0 (preparedInput P fee):=by
    apply frame.heapList prepared
    intro offset inside
    change offset<13 at inside
    omega
  have ptrBits : 1+natBits (96+(encodeList encodeEndpoint P.endpointCache.toList).length)≤endpointBudget P fee:=by
    rw [endpoint_heap_codec_length]
    have base:=base_cell_bits P fee
    have carry:=PDROC.EndpointOperands.carry_le_operandBudget P (inputBudget P fee)
    change 1+natBits (99+2*P.certificate.M)≤_ at base
    have normalized : 96+(2*P.certificate.M+3)=99+2*P.certificate.M:=by omega
    rw [normalized]
    exact base.trans carry
  let localEmit:=locatedBlock 295 (emitHeapCode 295 302).toArray
  have localEmitFetch : FetchesCode localEmit 295 (emitHeapCode 295 302):=by
    intro offset inside
    rw [locatedBlock_fetch,List.getElem?_toArray]
  obtain ⟨emitting,after,eh,el,ec,et,afterPC,_address,_index,heap,live,output,prefixes,emitSafe⟩:=
    emitHeap_trace_resources localEmit input 295 302 (endpointBudget P fee) localEmitFetch
      (encodeList encodeEndpoint P.endpointCache.toList) computed 96 computedPC computedAddress
      (by rw [endpoint_heap_codec_length];exact computedIndex) cache
      (calleeResources computed (List.mem_of_getLast? cl)).2
      ((natural 1 (by decide)).trans (PDROC.EndpointOperands.carry_le_operandBudget P _)) ptrBits
      (((by decide : natBits (295+7)≤64).trans small).trans (PDROC.EndpointOperands.carry_le_operandBudget P _))
      (((by decide : natBits 302≤64).trans small).trans (PDROC.EndpointOperands.carry_le_operandBudget P _))
  have emitFetch : FetchesCode program 295 (emitHeapCode 295 302):=by
    simpa only [endpointHeapArguments_length,RootD27.Endpoint.endpointCode_length] using fetch.append_right.append_right
  have emitted:=located_trace_in_program program input 295 (emitHeapCode 295 302) emitting emitFetch ec
  have emitScope : ∀ state∈emitting,295≤state.pc ∧ state.pc≤302:=by
    intro state member
    have split:=List.dropLast_append_getLast? after (by rw [el];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · have scope:=emitted.2.2 state proper
      change 295≤state.pc ∧ state.pc<295+7 at scope
      omega
    · have same:=List.mem_singleton.mp terminal
      subst state
      omega
  have first:=joinTrace_spec program input setup callee before entered computed 210
    (7000*(P.certificate.M+1)+15) sh sl ch cl sc embedded.1 st
    (embedded.2.1.trans (Nat.add_le_add_right ct 15))
  have joined:=joinTrace_spec program input (joinTrace setup callee) emitting before computed after
    (210+(7000*(P.certificate.M+1)+15)) (135*(2*P.certificate.M+3)+45)
    first.1 first.2.1 eh el first.2.2.1 emitted.1 first.2.2.2
    (by have cost:=emitted.2.1.trans (Nat.add_le_add_right et 15);rw [endpoint_heap_codec_length] at cost;omega)
  have allSafe:=PDCompute.Pack.joinTrace_invariant (joinTrace setup callee) emitting
    (fun state=>SafeBits state (endpointBudget P fee))
    (PDCompute.Pack.joinTrace_invariant setup callee (fun state=>SafeBits state (endpointBudget P fee))
      (fun state member=>PDCompute.Pack.safeBits_mono (setupResources state member).2
        (PDROC.EndpointOperands.carry_le_operandBudget P _)) (fun state member=>(calleeResources state member).2)) emitSafe
  have firstScope : ∀ state∈joinTrace setup callee,39≤state.pc ∧ state.pc≤295:=by
    intro state member
    rcases joinTrace_member member with early|later
    · have scope:=setupScope state early
      rw [endpointHeapArguments_length,position] at scope
      omega
    · have scope:=calleeScope state later
      omega
  have allScope : ∀ state∈joinTrace (joinTrace setup callee) emitting,39≤state.pc ∧ state.pc≤302:=by
    intro state member
    rcases joinTrace_member member with early|later
    · have scope:=firstScope state early;omega
    · have scope:=emitScope state later;omega
  refine ⟨joinTrace (joinTrace setup callee) emitting,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2.trans (by omega),afterPC,?_,?_,?_,?_,allSafe,allScope,?_,?_⟩
  · simpa only [HeapList,heapSegment,heap,live] using preparedComputed
  · simpa only [HeapList,heapSegment,heap,live] using cache
  · have enteredOutput : entered.output=before.output:=rfl
    simpa only [computedOutput,enteredOutput] using output
  · apply PDLower.CalibrationCompute.peakCells_le_of_forall
    intro state member
    rcases joinTrace_member member with early|later
    · rcases joinTrace_member early with setupMember|calleeMember
      · have memory:=(setupResources state setupMember).1
        simp only [workingCells,memory.2.1,memory.2.2]
        omega
      · have bound:=(workingCells_le_peak_of_member callee state calleeMember).trans calleePeak
        change workingCells state≤workingCells before+(2*P.certificate.M+51) at bound
        omega
    · have changed:=prefixes state later
      obtain ⟨written,pending,decomposition,stream⟩:=changed.2.2
      have outputBound : state.output.length≤computed.output.length+(encodeList encodeEndpoint P.endpointCache.toList).length:=by
        rw [stream,List.length_append]
        have length:=congrArg List.length decomposition
        simp only [List.length_append] at length
        omega
      have computedBound:=(workingCells_le_peak_of_member callee computed (List.mem_of_getLast? cl)).trans calleePeak
      change workingCells computed≤workingCells before+(2*P.certificate.M+51) at computedBound
      rw [endpoint_heap_codec_length] at outputBound
      simp only [workingCells,changed.2.1] at *
      omega
  · apply solverJoinTrace_proper (joinTrace setup callee) emitting computed (fun state=>state.pc<302) first.2.1 eh
    · intro state member;have scope:=firstScope state member;omega
    · intro state member
      have scope:=emitted.2.2 state member
      change 295≤state.pc ∧ state.pc<295+7 at scope
      omega

  · have noSetup : PaperProofs.Paid.Computation.entryCount 52 setup.dropLast=0:=
      (no_solve_entry ⟨52,0,0,0⟩ setup.dropLast (by
        intro state member
        have bound:=setupProper state member
        rw [endpointHeapArguments_length,position] at bound
        change state.pc≠52
        omega)).2
    have noEmit : PaperProofs.Paid.Computation.entryCount 52 emitting=0:=
      (no_solve_entry ⟨52,0,0,0⟩ emitting (by
        intro state member
        have bound:=emitScope state member
        change state.pc≠52
        omega)).2
    have firstCount : PaperProofs.Paid.Computation.entryCount 52 (joinTrace setup callee)=1:=by
      change PaperProofs.Paid.Computation.entryCount 52 (setup.dropLast++callee)=1
      rw [solveEntries_append ⟨52,0,0,0⟩,noSetup,calleeCount,Nat.zero_add]
    rw [entry_count_join 52 (joinTrace setup callee) emitting computed first.2.1 (by omega),firstCount,noEmit,Nat.add_zero]

end PDCompute.CorePrelude
