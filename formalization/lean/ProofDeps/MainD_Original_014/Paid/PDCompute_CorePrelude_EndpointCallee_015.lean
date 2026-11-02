module
public import Paid.PDCompute_CorePrelude_EndpointEntry_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
@[expose] public section

namespace PDCompute.CorePrelude
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver RootD27.Endpoint RootD27.Bits PDMenu.ComputeFrame PDROC.EndpointOperands PDROC.EndpointOperands.Loop
open RootD27.Core

/-- Original243 endpoint callee, at its actual fall-through returnPC.
The initialization and counted loop use their original numeric producers;
real local code scopes rule out a second entrance on this SAME witness. -/
theorem endpoint_callee_counted (P : Parameters) (program : Program) (input : List Cell)
    (origin : ℕ) (before : State) (base E budget : ℕ)
    (position : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (hE : before.register .address=.natural E) (hret : before.register .old=.natural (origin+243))
    (hgamma : before.register .total=.rational P.certificate.gamma)
    (hM : before.register .index=.natural P.certificate.M) (hfee : before.register .value=.rational P.reviewFee)
    (separated : base+48≤E) (fetched : FetchesCode program origin (endpointCode origin))
    (callerSafe : SafeBits before budget) (control : ControlBudget P origin base E (origin+243) budget)
    (rational : rationalBudget P≤budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤7000*(P.certificate.M+1) ∧ after.pc=origin+243 ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (origin+243) ∧
      after.register .address=.natural E ∧ after.register .index=.natural (2*P.certificate.M+3) ∧
      HeapList after E (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output=before.output ∧
      BelowBase before after base ∧ peakCells trace≤workingCells before+(2*P.certificate.M+51) ∧
      (∀ state∈trace,RegionMemory before state (endpointLoopRegion base E P.certificate.M) ∧ SafeBits state budget) ∧
      PaperProofs.Paid.Computation.entryCount origin trace=1 ∧
      (∀ state∈trace,origin≤state.pc ∧ state.pc≤origin+243) ∧
      (∀ state∈trace.dropLast,origin≤state.pc ∧ state.pc<origin+243) := by
  let localProgram:=locatedBlock origin (endpointCode origin).toArray
  let tailCode:=rowTestCode (origin+113) (origin+229)++(rowBodyCode (origin+105)++returnCode)
  let tailProgram:=locatedBlock (origin+105) tailCode.toArray
  have localFetch : FetchesCode localProgram origin (endpointCode origin):=by
    intro offset inside
    rw [locatedBlock_fetch,List.getElem?_toArray]
  have initialFetch : FetchesCode localProgram origin (initializationCode origin):=by
    have actual:=localFetch
    simp only [endpointCode,List.append_assoc] at actual
    exact actual.append_left
  obtain ⟨entry,middle,eh,el,ec,et,entryPC,entryFresh,entryHeader,invariant,stored,entryOutput,entryFrame,entryResources,
    entryCount,_entryProper⟩:=endpoint_entry_scoped P input origin before base E (origin+243) budget
      position fresh hE hret hgamma hM hfee separated callerSafe control rational
  have entryMoved:=located_trace_in_program localProgram input origin (initializationCode origin) entry initialFetch ec
  have tailFetch : FetchesCode tailProgram (origin+105) tailCode:=by
    intro offset inside
    rw [locatedBlock_fetch,List.getElem?_toArray]
  have testFetch : FetchesCode tailProgram (origin+105) (rowTestCode (origin+113) (origin+229)):=tailFetch.append_left
  have bodyFetch : FetchesCode tailProgram (origin+113) (rowBodyCode (origin+105)):=by
    simpa only [rowTestCode_length,Nat.add_assoc] using tailFetch.append_right.append_left
  have returnFetch : FetchesCode tailProgram (origin+229) returnCode:=by
    simpa only [rowTestCode_length,rowBodyCode_length,Nat.add_assoc] using tailFetch.append_right.append_right
  obtain ⟨loop,after,lh,ll,lc,lt,afterPC,afterFresh,afterOld,afterAddress,afterIndex,cache,loopOutput,loopFrame,loopMemory,loopSources⟩:=
    full_loop_sameBudget P tailProgram input origin base E (origin+243) budget separated testFetch bodyFetch returnFetch
      middle (loopEntryValues P before base) entryPC entryHeader entryFresh invariant stored
      (entryResources middle (List.mem_of_getLast? el)).2 control rational
  have tailInFull : FetchesCode localProgram (origin+105) tailCode:=by
    have actual:=localFetch
    simp only [endpointCode,List.append_assoc] at actual
    simpa only [initializationCode_length] using actual.append_right
  have loopMoved:=located_trace_in_program localProgram input (origin+105) tailCode loop tailInFull lc
  have noLoop : PaperProofs.Paid.Computation.entryCount origin loop=0:=by
    apply (no_solve_entry ⟨origin,0,0,0⟩ loop ?_).2
    intro state member
    have split:=List.dropLast_append_getLast? after (by rw [ll];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · have range:=loopMoved.2.2 state proper
      change state.pc≠origin
      omega
    · have same:=List.mem_singleton.mp terminal
      subst state
      change after.pc≠origin
      omega
  have joined:=joinTrace_spec localProgram input entry loop before middle after 4155
    (2370*(P.certificate.M+1)+375) eh el lh ll entryMoved.1 loopMoved.1
    (entryMoved.2.1.trans (Nat.add_le_add_right et 15)) (loopMoved.2.1.trans (Nat.add_le_add_right lt 15))
  have allMemory:=RegionMemory.join_trace entry loop before middle _ el
    (fun state member=>(entryResources state member).1) loopMemory
  have allSafe:=PDCompute.Pack.joinTrace_invariant entry loop (fun state=>SafeBits state budget)
    (fun state member=>(entryResources state member).2) (fun state member=>(loopSources state member).2)
  have moved:=located_trace_in_program program input origin (endpointCode origin) (joinTrace entry loop) fetched joined.2.2.1
  have counted : PaperProofs.Paid.Computation.entryCount origin (joinTrace entry loop)=1:=by
    rw [entry_count_join origin entry loop middle el (by omega),entryCount,noLoop,Nat.add_zero]
  have proper : ∀ state∈(joinTrace entry loop).dropLast,origin≤state.pc ∧ state.pc<origin+243:=by
    simpa only [endpointCode_length] using moved.2.2
  refine ⟨joinTrace entry loop,after,joined.1,joined.2.1,moved.1,
    moved.2.1.trans (Nat.add_le_add_right joined.2.2.2 15) |>.trans (by omega),afterPC,afterFresh,afterOld,
    afterAddress,afterIndex,cache,loopOutput.trans entryOutput,entryFrame.trans loopFrame,
    endpoint_region_peakCells _ before base E P.certificate.M allMemory,
    fun state member=>⟨allMemory state member,allSafe state member⟩,counted,?_,proper⟩
  intro state member
  have split:=List.dropLast_append_getLast? after (by rw [joined.2.1];simp)
  rw [←split] at member
  rcases List.mem_append.mp member with earlier|terminal
  · have range:=proper state earlier;omega
  · have same:=List.mem_singleton.mp terminal
    subst state
    omega

end PDCompute.CorePrelude
