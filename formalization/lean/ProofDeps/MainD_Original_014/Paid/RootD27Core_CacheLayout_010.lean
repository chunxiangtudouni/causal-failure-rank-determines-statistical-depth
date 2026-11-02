module

public import Paid.RootD27Core_SolverDispatch_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver

/-- Every ACTUAL endpoint-cache cell lies below the solver workspace,
for arbitrary DP dimensions. This is derived from the original codec
length and the actual computed base, not a caller disjointness oracle. -/
theorem original_endpoint_below_solver (P : Parameters) (offset : ℕ)
    (inside : offset<(encodeList encodeEndpoint P.endpointCache.toList).length) :
    96+offset<99+2*P.certificate.M := by
  rw [original_endpoint_codec_length] at inside
  omega

theorem original_endpoint_avoids_solver (P : Parameters) (n k offset : ℕ)
    (inside : offset<(encodeList encodeEndpoint P.endpointCache.toList).length) :
    96+offset∉workspace (99+2*P.certificate.M) n k := by
  intro member
  obtain ⟨position,_,address⟩:=Finset.mem_image.mp member
  have below:=original_endpoint_below_solver P offset inside
  omega

/-- Real caller argument setup/jumps preserve the actually computed
cache, which supplies the existing liveHeap solver reader interface. -/
theorem original_endpoint_source_transport (P : Parameters) (fee : ℚ) (before after : State)
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (heap : after.heap=before.heap) (live : after.live=before.live) :
    EndpointSource .liveHeap (preparedInput P fee) P 96 after := by
  change HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList)
  simpa only [HeapList,heapSegment,heap,live] using stored

end RootD27.Core
