module

public import Paid.RootD27Endpoint_Loop_019
public import Paid.RootD27Endpoint_Entry_021

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

theorem endpoint_budget_bound (m : ℕ) : 4140+(2370*(m+1)+360)≤7000*(m+1) := by omega

/-- A fixed243-opcode callee computes the complete original endpoint
cache. Its genuine caller arguments enter registers, not an answer cache
or a preinitialized header. The final jump is the actual indirect return. -/
theorem endpoint_callee_actual (P : Parameters) (program : Program) (input : List Cell)
    (origin : ℕ) (before : State) (base E returnPC : ℕ)
    (position : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (hE : before.register .address=.natural E) (hret : before.register .old=.natural returnPC)
    (hgamma : before.register .total=.rational P.certificate.gamma)
    (hM : before.register .index=.natural P.certificate.M)
    (hfee : before.register .value=.rational P.reviewFee)
    (separated : base+48≤E) (fetched : FetchesCode program origin (endpointCode origin)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤7000*(P.certificate.M+1) ∧ after.pc=returnPC ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural E ∧ after.register .index=.natural (2*P.certificate.M+3) ∧
      HeapList after E (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output=before.output := by
  obtain ⟨entryTrace,middle,eh,el,ec,et,entryPC,entryFresh,entryHeader,invariant,stored,entryOutput⟩:=
    entry_actual P program input origin before base E returnPC position fresh hE hret hgamma hM hfee separated fetched
  obtain ⟨loopTrace,after,lh,ll,lc,lt,afterPC,afterFresh,afterOld,afterAddress,afterIndex,cache,loopOutput⟩:=
    full_loop_original_cache P program input base E returnPC (origin+105) (origin+113) (origin+229)
      separated (endpoint_test_fetch program origin fetched) (endpoint_body_fetch program origin fetched)
      (endpoint_return_fetch program origin fetched) middle (loopEntryValues P before base)
      entryPC entryHeader entryFresh invariant stored
  have joined:=joinTrace_spec program input entryTrace loopTrace before middle after
    4140 (2370*(P.certificate.M+1)+360) eh el lh ll ec lc et lt
  refine ⟨joinTrace entryTrace loopTrace,after,joined.1,joined.2.1,joined.2.2.1,?_,
    afterPC,afterFresh,afterOld,afterAddress,afterIndex,cache,loopOutput.trans entryOutput⟩
  exact joined.2.2.2.trans (endpoint_budget_bound P.certificate.M)

theorem endpoint_callee_located (origin : ℕ) (P : Parameters) (input : List Cell)
    (before : State) (base E returnPC : ℕ)
    (position : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (hE : before.register .address=.natural E) (hret : before.register .old=.natural returnPC)
    (hgamma : before.register .total=.rational P.certificate.gamma)
    (hM : before.register .index=.natural P.certificate.M)
    (hfee : before.register .value=.rational P.reviewFee) (separated : base+48≤E) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step (locatedBlock origin (endpointProgram origin)) input first=some later) ∧
      time (locatedBlock origin (endpointProgram origin)) trace≤7000*(P.certificate.M+1) ∧ after.pc=returnPC ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural E ∧ after.register .index=.natural (2*P.certificate.M+3) ∧
      HeapList after E (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output=before.output :=
  endpoint_callee_actual P (locatedBlock origin (endpointProgram origin)) input origin before base E returnPC
    position fresh hE hret hgamma hM hfee separated (endpoint_located_fetch origin)

end RootD27.Endpoint
