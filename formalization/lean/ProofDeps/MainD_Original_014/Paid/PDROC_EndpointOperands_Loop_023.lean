module

public import Paid.PDROC_EndpointOperands_Loop_021
public import Paid.PDROC_EndpointOperands_Loop_022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver PDMenu.ComputeFrame RootD27.Bits

/-- ONE actual complete M+1-row/cache/return witness, pointwise
strengthened by the canonical-source induction to SAME caller B. -/
theorem full_loop_sameBudget (P : Parameters) (program : Program) (input : List Cell)
    (origin base E returnPC budget : ℕ) (separated : base + 48 ≤ E)
    (testFetch : FetchesCode program (origin + 105) (rowTestCode (origin + 113) (origin + 229)))
    (bodyFetch : FetchesCode program (origin + 113) (rowBodyCode (origin + 105)))
    (returnFetch : FetchesCode program (origin + 229) returnCode)
    (before : State) (values : ℕ → Cell) (position : before.pc = origin + 105)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (invariant : EndpointValues P E returnPC 0 values) (stored : StoredCache P E 0 before)
    (callerSafe : SafeBits before budget) (control : ControlBudget P origin base E returnPC budget)
    (rational : rationalBudget P ≤ budget) :
    ∃ trace : List State, ∃ after : State,
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun first later => step program input first = some later) ∧
      time program trace ≤ 2370 * (P.certificate.M + 1) + 360 ∧ after.pc = returnPC ∧
      after.register .fresh = .natural base ∧ after.register .old = .natural returnPC ∧
      after.register .address = .natural E ∧ after.register .index = .natural (2 * P.certificate.M + 3) ∧
      HeapList after E (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output = before.output ∧
      BelowBase before after base ∧
      (∀ state ∈ trace, RegionMemory before state (endpointLoopRegion base E P.certificate.M)) ∧
      (∀ state ∈ trace, LoopProvenance P program input base E returnPC (origin + 105) (origin + 113) (origin + 229) before state ∧
        SafeBits state budget) := by
  obtain ⟨trace, after, head, last, chain, cost, pc, nextFresh, old, address, index, cache,
    output, frame, memory, provenance⟩ := full_loop_original_cache_provenance P program input
      base E returnPC (origin + 105) (origin + 113) (origin + 229) separated testFetch bodyFetch returnFetch
      before values position header fresh invariant stored
  refine ⟨trace, after, head, last, chain, cost, pc, nextFresh, old, address, index, cache, output, frame, memory, ?_⟩
  intro state member
  exact ⟨provenance state member, loopProvenance_safe P program input origin base E returnPC budget before state
    separated callerSafe control rational (provenance state member)⟩

end PDROC.EndpointOperands.Loop
