module

public import Paid.RootD27Endpoint_Callee_022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

/-- Preserve the actually stored prepared-input prefix below the callee
workspace. Both live membership and the original heap value are exact. -/
def BelowBase (before after : State) (base : ℕ) : Prop :=
  ∀ address,address<base → after.heap address=before.heap address ∧
    (address∈after.live ↔ address∈before.live)

theorem BelowBase.refl (before : State) (base : ℕ) : BelowBase before before base :=
  fun _ _ => ⟨rfl,Iff.rfl⟩

theorem BelowBase.trans {before middle after : State} {base : ℕ}
    (first : BelowBase before middle base) (later : BelowBase middle after base) :
    BelowBase before after base := by
  intro address inside
  exact ⟨(later address inside).1.trans (first address inside).1,
    (later address inside).2.trans (first address inside).2⟩

theorem BelowBase.of_unchanged {before after : State} (base : ℕ)
    (heap : after.heap=before.heap) (live : after.live=before.live) : BelowBase before after base := by
  intro address _
  exact ⟨congrFun heap address,by rw [live]⟩

theorem BelowBase.heapList {before after : State} {base pointer : ℕ} {cells : List Cell}
    (frame : BelowBase before after base) (stored : HeapList before pointer cells)
    (inside : ∀ offset<cells.length,pointer+offset<base) : HeapList after pointer cells := by
  apply PDLower.CalibrationCompute.HeapList.of_values
  · intro offset bound
    exact ((frame (pointer+offset) (inside offset bound)).2).mpr (stored.1 offset bound)
  · intro offset bound
    exact ((frame (pointer+offset) (inside offset bound)).1).trans
      (PDLower.CalibrationCompute.HeapList.value stored offset bound)

theorem belowBase_of_solverFrame {before after : State} {base n k : ℕ}
    (frame : PDCompute.Solver.Frame before after base n k) : BelowBase before after base := by
  intro address inside
  have outside : address∉workspace base n k := by
    intro member
    obtain ⟨offset,_,eq⟩:=Finset.mem_image.mp member
    omega
  exact ⟨frame.1 address outside,frame.2 address outside⟩

theorem cacheHeader_below (before : State) (base M E : ℕ) (separated : base+48≤E) :
    BelowBase before (cacheHeaderResult before base M E) base := by
  intro address inside
  constructor
  · rw [cacheHeader_heap,Function.update_of_ne (by omega : address≠E),
      Function.update_of_ne (by omega : address≠base+17)]
  · rw [cacheHeader_live]
    simp only [Finset.mem_insert,show address≠E from by omega,
      show address≠base+17 from by omega,false_or]

theorem rowBody_below {before after : State} {base E m : ℕ} (separated : base+48≤E)
    (frame : ∀ address,address<base ∨ base+48≤address →
      address≠E+1+2*m → address≠E+2+2*m → after.heap address=before.heap address)
    (live : after.live=insert (E+2+2*m) (insert (E+1+2*m) before.live)) :
    BelowBase before after base := by
  intro address inside
  constructor
  · exact frame address (Or.inl inside) (by omega) (by omega)
  · rw [live]
    simp only [Finset.mem_insert,show address≠E+2+2*m from by omega,
      show address≠E+1+2*m from by omega,false_or]

/-- Same real row witness simultaneously carries the original cache
invariant and preservation of the genuine prepared-input memory. -/
theorem EndpointValues.actual_body_cache_frame (P : Parameters) (m : ℕ) (program : Program) (input : List Cell)
    (before : State) (base E returnPC testPC : ℕ) (values : ℕ→Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (invariant : EndpointValues P E returnPC m values) (stored : StoredCache P E m before)
    (separated : base+48≤E) (fetched : FetchesCode program before.pc (rowBodyCode testPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤2235 ∧ after.pc=testPC ∧ after.register .fresh=.natural base ∧
      Header after base (bodyValues P values m) ∧ EndpointValues P E returnPC (m+1) (bodyValues P values m) ∧
      StoredCache P E (m+1) after ∧ after.output=before.output ∧ BelowBase before after base := by
  obtain ⟨trace,after,head,last,chain,cost,pc,nextFresh,nextHeader,l1,l2,v1,v2,frame,live,output⟩:=
    rowBody_actual_frame P m program input before base E testPC values header fresh
      invariant.cache invariant.counter invariant.one invariant.two invariant.power invariant.odds
      invariant.fee invariant.denominator separated fetched
  exact ⟨trace,after,head,last,chain,cost,pc,nextFresh,nextHeader,invariant.body,
    stored.advance separated ⟨l1,l2,v1,v2⟩ frame live,output,rowBody_below separated frame live⟩

end RootD27.Endpoint
