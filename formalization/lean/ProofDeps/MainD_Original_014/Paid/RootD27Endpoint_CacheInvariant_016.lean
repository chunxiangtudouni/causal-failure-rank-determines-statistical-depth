module

public import Paid.RootD27Endpoint_LoopValues_014
public import Paid.RootD27Endpoint_RowFrame_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

/-- Precisely the cache cells that have already been physically written.
No assumption about future rows or a supplied serialized answer. -/
structure StoredCache (P : Parameters) (E m : ℕ) (state : State) : Prop where
  header_live : E∈state.live
  header_value : state.heap E=.natural (P.certificate.M+1)
  rows : ∀ row < m,
    E+1+2*row∈state.live ∧ E+2+2*row∈state.live ∧
    state.heap (E+1+2*row)=.rational (P.endpointConstant row).error ∧
    state.heap (E+2+2*row)=.rational (P.endpointConstant row).charge

theorem StoredCache.initial (P : Parameters) (E : ℕ) (state : State)
    (live : E∈state.live) (value : state.heap E=.natural (P.certificate.M+1)) :
    StoredCache P E 0 state := by
  refine ⟨live,value,?_⟩
  intro row impossible
  omega

theorem StoredCache.congr {P : Parameters} {E m : ℕ} {before after : State}
    (stored : StoredCache P E m before) (heap : after.heap=before.heap) (live : after.live=before.live) :
    StoredCache P E m after := by
  constructor
  · simpa only [live] using stored.header_live
  · simpa only [heap] using stored.header_value
  · intro row bound
    simpa only [heap,live] using stored.rows row bound

theorem StoredCache.advance {P : Parameters} {E m base : ℕ} {before after : State}
    (stored : StoredCache P E m before) (separated : base+48≤E)
    (cells : E+1+2*m∈after.live ∧ E+2+2*m∈after.live ∧
      after.heap (E+1+2*m)=.rational (P.endpointConstant m).error ∧
      after.heap (E+2+2*m)=.rational (P.endpointConstant m).charge)
    (frame : ∀ address, address<base ∨ base+48≤address →
      address≠E+1+2*m → address≠E+2+2*m → after.heap address=before.heap address)
    (live : after.live=insert (E+2+2*m) (insert (E+1+2*m) before.live)) :
    StoredCache P E (m+1) after := by
  constructor
  · rw [live]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem stored.header_live)
  · exact (frame E (Or.inr separated) (by omega) (by omega)).trans stored.header_value
  · intro row bound
    by_cases same : row=m
    · subst row
      exact cells
    · have old : row<m := by omega
      obtain ⟨firstLive,lastLive,firstValue,lastValue⟩:=stored.rows row old
      refine ⟨?_,?_,?_,?_⟩
      · rw [live]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem firstLive)
      · rw [live]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem lastLive)
      · exact (frame (E+1+2*row) (Or.inr (by omega)) (by omega) (by omega)).trans firstValue
      · exact (frame (E+2+2*row) (Or.inr (by omega)) (by omega) (by omega)).trans lastValue

theorem EndpointValues.cache_header {P : Parameters} {E returnPC m : ℕ} {values : ℕ → Cell}
    (invariant : EndpointValues P E returnPC m values) :
    EndpointValues P E returnPC m (Function.update values 17 (.natural (P.certificate.M+1))) := by
  rcases invariant with ⟨cache,ret,gamma,stop,fee,odds,power,counter,denominator,one,two⟩
  constructor <;> simp_all

theorem EndpointValues.actual_body_cache (P : Parameters) (m : ℕ) (program : Program) (input : List Cell)
    (before : State) (base E returnPC testPC : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (invariant : EndpointValues P E returnPC m values) (stored : StoredCache P E m before)
    (separated : base+48≤E) (hfetch : FetchesCode program before.pc (rowBodyCode testPC)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤2235 ∧ after.pc=testPC ∧ after.register .fresh=.natural base ∧
      Header after base (bodyValues P values m) ∧
      EndpointValues P E returnPC (m+1) (bodyValues P values m) ∧ StoredCache P E (m+1) after ∧
      after.output=before.output := by
  obtain ⟨trace,after,hh,hl,hc,ht,hp,hb,headerAfter,l1,l2,v1,v2,frame,live,output⟩:=
    rowBody_actual_frame P m program input before base E testPC values header hbase
      invariant.cache invariant.counter invariant.one invariant.two invariant.power
      invariant.odds invariant.fee invariant.denominator separated hfetch
  exact ⟨trace,after,hh,hl,hc,ht,hp,hb,headerAfter,invariant.body,
    stored.advance separated ⟨l1,l2,v1,v2⟩ frame live,output⟩

end RootD27.Endpoint
