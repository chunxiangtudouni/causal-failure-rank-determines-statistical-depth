module

public import Paid.RootD27Endpoint_Code_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute

def endpointPrefix (P : Parameters) (m : ℕ) : List Cell :=
  .natural (P.certificate.M+1)::(List.range m).flatMap (fun row => encodeEndpoint (P.endpointConstant row))

theorem endpointPrefix_zero (P : Parameters) : endpointPrefix P 0=[.natural (P.certificate.M+1)] := rfl

theorem endpointPrefix_succ (P : Parameters) (m : ℕ) :
    endpointPrefix P (m+1)=endpointPrefix P m++
      [.rational (P.endpointConstant m).error,.rational (P.endpointConstant m).charge] := by
  simp [endpointPrefix,List.range_succ,List.flatMap_append,encodeEndpoint]

theorem endpointPrefix_length (P : Parameters) (m : ℕ) : (endpointPrefix P m).length=2*m+1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [endpointPrefix_succ,List.length_append,ih]
      simp only [List.length_cons,List.length_nil]
      omega

theorem original_endpoints_toList (P : Parameters) :
    P.endpointCache.toList=(List.range (P.certificate.M+1)).map P.endpointConstant := by
  apply List.ext_getElem (by simp [Parameters.endpointCache_size])
  intro index first second
  simp only [Array.getElem_toList,Parameters.endpointCache,Array.getElem_ofFn,
    List.getElem_map,List.getElem_range]

theorem endpointPrefix_original (P : Parameters) :
    endpointPrefix P (P.certificate.M+1)=encodeList encodeEndpoint P.endpointCache.toList := by
  rw [original_endpoints_toList]
  simp [endpointPrefix,encodeList,List.flatMap_map]

/-- Concatenate already established physical heap segments. This is a
representation lemma; the actual caller still supplies both real stores. -/
theorem heapList_append {state : State} {base : ℕ} {first later : List Cell}
    (left : HeapList state base first) (right : HeapList state (base+first.length) later) :
    HeapList state base (first++later) := by
  apply HeapList.of_values
  · intro index inside
    by_cases old : index<first.length
    · exact left.1 index old
    · have bound : index-first.length<later.length := by
        simp only [List.length_append] at inside
        omega
      have address : base+first.length+(index-first.length)=base+index := by omega
      simpa only [address] using right.1 (index-first.length) bound
  · intro index inside
    by_cases old : index<first.length
    · rw [List.getElem_append_left old]
      exact left.value index old
    · have bound : index-first.length<later.length := by
        simp only [List.length_append] at inside
        omega
      rw [List.getElem_append_right (by omega)]
      have address : base+first.length+(index-first.length)=base+index := by omega
      simpa only [address] using right.value (index-first.length) bound

end RootD27.Endpoint
