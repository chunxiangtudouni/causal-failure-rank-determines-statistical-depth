module

public import Paid.PDROC_EndpointOperands_Loop_020

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver PDMenu.ComputeFrame

/-- Complete ORIGINAL M+1-row loop with canonical sources on its SAME
functional/cache/frame/time/actual-return witness. Good and closure are
instantiated by constructors, not supplied as original caller premises. -/
theorem full_loop_original_cache_provenance (P : Parameters) (program : Program) (input : List Cell)
    (base E returnPC testPC bodyPC exitPC : ℕ) (separated : base + 48 ≤ E)
    (testFetch : FetchesCode program testPC (rowTestCode bodyPC exitPC))
    (bodyFetch : FetchesCode program bodyPC (rowBodyCode testPC))
    (returnFetch : FetchesCode program exitPC returnCode)
    (before : State) (values : ℕ → Cell) (position : before.pc = testPC)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (invariant : EndpointValues P E returnPC 0 values) (stored : StoredCache P E 0 before) :
    ∃ trace : List State, ∃ after : State,
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun first later => step program input first = some later) ∧
      time program trace ≤ 2370 * (P.certificate.M + 1) + 360 ∧ after.pc = returnPC ∧
      after.register .fresh = .natural base ∧ after.register .old = .natural returnPC ∧
      after.register .address = .natural E ∧ after.register .index = .natural (2 * P.certificate.M + 3) ∧
      HeapList after E (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output = before.output ∧
      BelowBase before after base ∧
      (∀ state ∈ trace, RegionMemory before state (endpointLoopRegion base E P.certificate.M)) ∧
      (∀ state ∈ trace, LoopProvenance P program input base E returnPC testPC bodyPC exitPC before state) := by
  obtain ⟨trace, after, head, last, chain, cost, pc, nextFresh, old, address, index, storedAfter,
    output, frame, memory, provenance⟩ := loop_cache_actual_closed P program input base E returnPC testPC bodyPC exitPC
      separated testFetch bodyFetch returnFetch
      (LoopProvenance P program input base E returnPC testPC bodyPC exitPC before)
      (loopProvenance_closed P program input base E returnPC testPC bodyPC exitPC before)
      (P.certificate.M + 1) 0 before values position header fresh invariant stored (by omega) LoopProvenance.initial
  exact ⟨trace, after, head, last, chain, cost, pc, nextFresh, old, address, index,
    storedAfter.original_codec, output, frame, memory, provenance⟩

end PDROC.EndpointOperands.Loop
