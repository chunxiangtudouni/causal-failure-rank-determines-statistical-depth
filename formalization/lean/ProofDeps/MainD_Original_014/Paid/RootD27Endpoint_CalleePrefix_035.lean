module

public import Paid.RootD27Endpoint_LoopPrefix_031
public import Paid.RootD27Endpoint_EntryPrefix_034

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

/-- Full original actual endpoint callee and its genuine below-workspace
memory frame on ONE trace. Caller prepared data are never recomputed. -/
theorem endpoint_callee_actual_region (P : Parameters) (program : Program) (input : List Cell)
    (origin : ℕ) (before : State) (base E returnPC : ℕ)
    (position : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (hE : before.register .address=.natural E) (hret : before.register .old=.natural returnPC)
    (hgamma : before.register .total=.rational P.certificate.gamma)
    (hM : before.register .index=.natural P.certificate.M)
    (hfee : before.register .value=.rational P.reviewFee)
    (separated : base+48≤E) (fetched : FetchesCode program origin (endpointCode origin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤7000*(P.certificate.M+1) ∧ after.pc=returnPC ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural E ∧ after.register .index=.natural (2*P.certificate.M+3) ∧
      HeapList after E (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output=before.output ∧
      BelowBase before after base ∧
      (∀ state∈trace,RegionMemory before state (endpointLoopRegion base E P.certificate.M)) := by
  obtain ⟨entryTrace,middle,eh,el,ec,et,entryPC,entryFresh,entryHeader,invariant,stored,entryOutput,entryFrame,entryPrefixes⟩:=
    entry_actual_region P program input origin before base E returnPC position fresh hE hret hgamma hM hfee separated fetched
  obtain ⟨loopTrace,after,lh,ll,lc,lt,afterPC,afterFresh,afterOld,afterAddress,afterIndex,cache,loopOutput,loopFrame,loopPrefixes⟩:=
    full_loop_original_cache_region P program input base E returnPC (origin+105) (origin+113) (origin+229)
      separated (endpoint_test_fetch program origin fetched) (endpoint_body_fetch program origin fetched)
      (endpoint_return_fetch program origin fetched) middle (loopEntryValues P before base)
      entryPC entryHeader entryFresh invariant stored
  have joined:=joinTrace_spec program input entryTrace loopTrace before middle after
    4140 (2370*(P.certificate.M+1)+360) eh el lh ll ec lc et lt
  exact ⟨joinTrace entryTrace loopTrace,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2.trans (endpoint_budget_bound P.certificate.M),afterPC,afterFresh,afterOld,afterAddress,
    afterIndex,cache,loopOutput.trans entryOutput,entryFrame.trans loopFrame,RegionMemory.join_trace entryTrace loopTrace before middle _ el entryPrefixes loopPrefixes⟩

end RootD27.Endpoint
