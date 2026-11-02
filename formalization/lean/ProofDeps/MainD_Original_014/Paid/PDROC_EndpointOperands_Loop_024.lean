module

public import Paid.PDROC_EndpointOperands_Loop_023
public import Paid.PDROC_EndpointOperands_Entry_003
public import Paid.PDROC_D27Prepare_Resources_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1300000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver PDMenu.ComputeFrame RootD27.Bits

/-- Entire ORIGINAL243-op endpoint callee: ONE strengthened actual entry
witness joins ONE canonical M+1-row/real-return witness. The same joined
trace simultaneously has original functionality/time/frame/caller-relative
space and SAME caller-B operand bits at EVERY actual fetched prefix.
Arbitrary old scratch/live/output cells are carried by callerSafe, not
given a new parameter-only qualification. -/
theorem endpoint_callee_sameBudget (P : Parameters) (program : Program) (input : List Cell)
    (origin : ℕ) (before : State) (base E returnPC budget : ℕ)
    (position : before.pc = origin) (fresh : before.register .fresh = .natural base)
    (hE : before.register .address = .natural E) (hret : before.register .old = .natural returnPC)
    (hgamma : before.register .total = .rational P.certificate.gamma)
    (hM : before.register .index = .natural P.certificate.M)
    (hfee : before.register .value = .rational P.reviewFee)
    (separated : base + 48 ≤ E) (fetched : FetchesCode program origin (endpointCode origin))
    (callerSafe : SafeBits before budget) (control : ControlBudget P origin base E returnPC budget)
    (rational : rationalBudget P ≤ budget) :
    ∃ trace : List State, ∃ after : State,
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun first later => step program input first = some later) ∧
      time program trace ≤ 7000 * (P.certificate.M + 1) ∧ after.pc = returnPC ∧
      after.register .fresh = .natural base ∧ after.register .old = .natural returnPC ∧
      after.register .address = .natural E ∧ after.register .index = .natural (2 * P.certificate.M + 3) ∧
      HeapList after E (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output = before.output ∧
      BelowBase before after base ∧
      peakCells trace ≤ workingCells before + (2 * P.certificate.M + 51) ∧ peakOperandBits trace ≤ budget ∧
      ∀ state ∈ trace, RegionMemory before state (endpointLoopRegion base E P.certificate.M) ∧ SafeBits state budget := by
  obtain ⟨entryTrace, middle, eh, el, ec, et, entryPC, entryFresh, entryHeader, invariant, stored,
    entryOutput, entryFrame, entryPrefixes⟩ := entry_actual_sameBudget P program input origin before base E returnPC budget
      position fresh hE hret hgamma hM hfee separated fetched callerSafe control rational
  have middleSafe := (entryPrefixes middle (List.mem_of_getLast? el)).2
  obtain ⟨loopTrace, after, lh, ll, lc, lt, afterPC, afterFresh, afterOld, afterAddress, afterIndex, cache,
    loopOutput, loopFrame, loopMemory, loopSources⟩ := full_loop_sameBudget P program input origin base E returnPC budget
      separated (endpoint_test_fetch program origin fetched) (endpoint_body_fetch program origin fetched)
      (endpoint_return_fetch program origin fetched) middle (loopEntryValues P before base)
      entryPC entryHeader entryFresh invariant stored middleSafe control rational
  have joined := joinTrace_spec program input entryTrace loopTrace before middle after
    4140 (2370 * (P.certificate.M + 1) + 360) eh el lh ll ec lc et lt
  have memory := RegionMemory.join_trace entryTrace loopTrace before middle _ el
    (fun state member => (entryPrefixes state member).1) loopMemory
  have safe := PDCompute.Pack.joinTrace_invariant entryTrace loopTrace (fun state => SafeBits state budget)
    (fun state member => (entryPrefixes state member).2) (fun state member => (loopSources state member).2)
  have space := endpoint_region_peakCells (joinTrace entryTrace loopTrace) before base E P.certificate.M memory
  have operands := PDROC.D27Prepare.Resources.peakOperandBits_le_of_states (joinTrace entryTrace loopTrace) budget safe
  refine ⟨joinTrace entryTrace loopTrace, after, joined.1, joined.2.1, joined.2.2.1,
    joined.2.2.2.trans (endpoint_budget_bound P.certificate.M), afterPC, afterFresh, afterOld, afterAddress, afterIndex,
    cache, loopOutput.trans entryOutput, entryFrame.trans loopFrame, space, operands, ?_⟩
  intro state member
  exact ⟨memory state member, safe state member⟩

end PDROC.EndpointOperands.Loop
