module

public import Paid.PDLower_CalibrationCompute_HeapList_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem flatMapPair_first {α : Type*} (left right : α→Cell) (values : List α) (index : ℕ)
    (inside : index<values.length) :
    (values.flatMap (fun value => [left value,right value]))[2*index]?=some (left values[index]) := by
  induction values generalizing index with
  | nil => simp at inside
  | cons head tail ih =>
    cases index with
    | zero => rfl
    | succ index =>
      have bound : index<tail.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using inside
      have position : 2*(index+1)=2*index+2 := by omega
      simpa only [position,List.flatMap_cons,List.cons_append,List.nil_append,List.getElem?_cons_succ,
        List.getElem_cons_succ] using ih index bound

theorem endpointCache_error_lookup (P : Parameters) (m : ℕ) (inside : m<P.certificate.M+1) :
    (encodeList encodeEndpoint P.endpointCache.toList)[1+2*m]?=
      some (.rational (P.endpointConstant m).error) := by
  have bound : m<P.endpointCache.toList.length := by simpa using inside
  have lookup := flatMapPair_first (fun e : EndpointConstant => Cell.rational e.error)
    (fun e => Cell.rational e.charge) P.endpointCache.toList m bound
  have value : P.endpointCache.toList[m]=(P.endpointConstant m) := by
    simp only [Array.getElem_toList,Parameters.endpointCache,Array.getElem_ofFn]
  have encoder : encodeEndpoint=(fun endpoint : EndpointConstant => [.rational endpoint.error,.rational endpoint.charge]) := rfl
  rw [encoder]
  simpa only [encodeList,Nat.add_comm 1,List.getElem?_cons_succ,value] using lookup

/-- This derives the scalar weight block's live lookup from the ORIGINAL
encoded endpoint cache; no error value is appended to the call interface. -/
theorem endpointHeap_error {P : Parameters} {state : State} {endpoints level : ℕ}
    (cache : HeapList state endpoints (encodeList encodeEndpoint P.endpointCache.toList))
    (positive : 0<level) (bounded : level≤P.certificate.M+1) :
    endpoints+(level*2-1) ∈ state.live ∧
      state.heap (endpoints+(level*2-1))=.rational (P.endpointConstant (level-1)).error := by
  have bound : level-1<P.certificate.M+1 := by omega
  have lookup := endpointCache_error_lookup P (level-1) bound
  obtain ⟨inside,value⟩ := List.getElem?_eq_some_iff.mp lookup
  have position : 1+2*(level-1)=level*2-1 := by omega
  constructor
  · simpa only [position] using cache.1 (1+2*(level-1)) inside
  · simpa only [position] using (HeapList.value cache (1+2*(level-1)) inside).trans value

end PDLower.CalibrationCompute
