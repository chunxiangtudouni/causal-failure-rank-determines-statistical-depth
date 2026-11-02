module

public import Paid.RootD27Endpoint_BelowFrame_023
public import Paid.RootD27Endpoint_RowPrefix_029

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

def endpointLoopRegion (base E M : ℕ) : Finset ℕ :=
  cellRegion base headerWords ∪ cellRegion E (2*M+3)

theorem endpointRowRegion_subset_loop (base E m M : ℕ) (bound : m≤M) :
    endpointRowRegion base E m⊆endpointLoopRegion base E M :=
  Finset.union_subset_union (Finset.Subset.refl _) (pair_region_inside_cache E m M bound)

/-- Same real row witness simultaneously carries the original cache
invariant and preservation of the genuine prepared-input memory. -/
theorem EndpointValues.actual_body_cache_region (P : Parameters) (m : ℕ) (program : Program) (input : List Cell)
    (before : State) (base E returnPC testPC : ℕ) (values : ℕ→Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (invariant : EndpointValues P E returnPC m values) (stored : StoredCache P E m before)
    (separated : base+48≤E) (fetched : FetchesCode program before.pc (rowBodyCode testPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤2235 ∧ after.pc=testPC ∧ after.register .fresh=.natural base ∧
      Header after base (bodyValues P values m) ∧ EndpointValues P E returnPC (m+1) (bodyValues P values m) ∧
      StoredCache P E (m+1) after ∧ after.output=before.output ∧ BelowBase before after base ∧
      (∀ state∈trace,RegionMemory before state (endpointRowRegion base E m)) := by
  obtain ⟨trace,after,head,last,chain,cost,pc,nextFresh,nextHeader,l1,l2,v1,v2,frame,live,output,prefixes⟩:=
    rowBody_actual_region P m program input before base E testPC values header fresh
      invariant.cache invariant.counter invariant.one invariant.two invariant.power invariant.odds
      invariant.fee invariant.denominator separated fetched
  exact ⟨trace,after,head,last,chain,cost,pc,nextFresh,nextHeader,invariant.body,
    stored.advance separated ⟨l1,l2,v1,v2⟩ frame live,output,rowBody_below separated frame live,prefixes⟩

end RootD27.Endpoint
