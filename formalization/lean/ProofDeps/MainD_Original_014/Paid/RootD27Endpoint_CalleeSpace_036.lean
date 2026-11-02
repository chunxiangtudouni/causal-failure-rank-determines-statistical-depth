module

public import Paid.RootD27Endpoint_CalleePrefix_035

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

theorem endpoint_region_peakCells (trace : List State) (before : State) (base E M : ℕ)
    (memory : ∀ state∈trace,RegionMemory before state (endpointLoopRegion base E M)) :
    peakCells trace≤workingCells before+(2*M+51) := by
  by_cases empty : trace=[]
  · simp only [empty,peakCells,List.map_nil,List.foldl_nil]
    omega
  · have nonempty : trace.map workingCells≠[] := by
      intro mapped
      have length:=congrArg List.length mapped
      have zero : trace.length=0 := by simpa only [List.length_map,List.length_nil] using length
      exact empty (List.length_eq_zero_iff.mp zero)
    unfold peakCells
    rw [List.foldl_max_eq_max nonempty]
    apply max_le (Nat.zero_le _)
    apply (List.max_le_iff nonempty).mpr
    intro value member
    obtain ⟨state,inside,rfl⟩:=List.mem_map.mp member
    exact endpoint_loop_workingCells before state base E M (memory state inside)

/-- Entire original243-op endpoint callee, including true37-op header
allocation, original scalar setup, real cache header, all M+1 rows and
actual indirect return, with a SAME-trace all-prefix peak-space bound.
Old live caller cells and output remain counted; no bit-budget premise. -/
theorem endpoint_callee_actual_space (P : Parameters) (program : Program) (input : List Cell)
    (origin : ℕ) (before : State) (base E returnPC : ℕ)
    (position : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (hE : before.register .address=.natural E) (hret : before.register .old=.natural returnPC)
    (hgamma : before.register .total=.rational P.certificate.gamma)
    (hM : before.register .index=.natural P.certificate.M)
    (hfee : before.register .value=.rational P.reviewFee)
    (separated : base+48≤E) (fetched : FetchesCode program origin (endpointCode origin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤7000*(P.certificate.M+1) ∧ after.pc=returnPC ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural E ∧ after.register .index=.natural (2*P.certificate.M+3) ∧
      HeapList after E (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output=before.output ∧
      BelowBase before after base ∧
      peakCells trace≤workingCells before+(2*P.certificate.M+51) ∧
      ∀ state∈trace,RegionMemory before state (endpointLoopRegion base E P.certificate.M) := by
  obtain ⟨trace,after,head,last,chain,cost,pc,nextFresh,old,address,index,cache,output,frame,prefixes⟩:=
    endpoint_callee_actual_region P program input origin before base E returnPC position fresh hE hret hgamma hM hfee separated fetched
  exact ⟨trace,after,head,last,chain,cost,pc,nextFresh,old,address,index,cache,output,frame,
    endpoint_region_peakCells trace before base E P.certificate.M prefixes,prefixes⟩

end RootD27.Endpoint
