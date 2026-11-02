module

public import Paid.RootD27Endpoint_CacheInvariant_016
public import Paid.RootD27Endpoint_CacheCodec_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDLower.CalibrationCompute

theorem endpointPrefix_head (P : Parameters) (m : ℕ) :
    (endpointPrefix P m)[0]'(by rw [endpointPrefix_length]; omega)=.natural (P.certificate.M+1) := rfl

theorem endpointPrefix_error (P : Parameters) (m row : ℕ) (inside : row<m) :
    (endpointPrefix P m)[1+2*row]'(by rw [endpointPrefix_length]; omega)=
      .rational (P.endpointConstant row).error := by
  induction m generalizing row with
  | zero => omega
  | succ m ih =>
    by_cases old : row<m
    · simp only [endpointPrefix_succ]
      rw [List.getElem_append_left (by rw [endpointPrefix_length]; omega)]
      exact ih row old
    · have last : row=m := by omega
      subst row
      simp only [endpointPrefix_succ]
      rw [List.getElem_append_right (by rw [endpointPrefix_length]; omega)]
      have difference : 1+2*m-(endpointPrefix P m).length=0 := by rw [endpointPrefix_length]; omega
      simp only [difference,List.getElem_cons_zero]

theorem endpointPrefix_charge (P : Parameters) (m row : ℕ) (inside : row<m) :
    (endpointPrefix P m)[2+2*row]'(by rw [endpointPrefix_length]; omega)=
      .rational (P.endpointConstant row).charge := by
  induction m generalizing row with
  | zero => omega
  | succ m ih =>
    by_cases old : row<m
    · simp only [endpointPrefix_succ]
      rw [List.getElem_append_left (by rw [endpointPrefix_length]; omega)]
      exact ih row old
    · have last : row=m := by omega
      subst row
      simp only [endpointPrefix_succ]
      rw [List.getElem_append_right (by rw [endpointPrefix_length]; omega)]
      have difference : 2+2*m-(endpointPrefix P m).length=1 := by rw [endpointPrefix_length]; omega
      simp only [difference,List.getElem_cons_succ,List.getElem_cons_zero]

/-- All physically stored row cells imply the exact original prefix
codec; every cell and every live address is checked. -/
theorem StoredCache.heapPrefix {P : Parameters} {E m : ℕ} {state : State}
    (stored : StoredCache P E m state) : HeapList state E (endpointPrefix P m) := by
  apply HeapList.of_values
  · intro index bound
    have lengthBound : index<2*m+1 := by simpa only [endpointPrefix_length] using bound
    by_cases zero : index=0
    · subst index
      simpa only [Nat.add_zero] using stored.header_live
    · let row:=(index-1)/2
      have inside : row<m := by dsimp only [row]; omega
      have split : index=1+2*row ∨ index=2+2*row := by dsimp only [row]; omega
      rcases split with first|later
      · rw [first]
        simpa only [Nat.add_assoc] using (stored.rows row inside).1
      · rw [later]
        simpa only [Nat.add_assoc] using (stored.rows row inside).2.1
  · intro index bound
    have lengthBound : index<2*m+1 := by simpa only [endpointPrefix_length] using bound
    by_cases zero : index=0
    · subst index
      rw [endpointPrefix_head]
      simpa only [Nat.add_zero] using stored.header_value
    · let row:=(index-1)/2
      have inside : row<m := by dsimp only [row]; omega
      have split : index=1+2*row ∨ index=2+2*row := by dsimp only [row]; omega
      rcases split with first|later
      · simp only [first]
        rw [endpointPrefix_error P m row inside]
        simpa only [Nat.add_assoc] using (stored.rows row inside).2.2.1
      · simp only [later]
        rw [endpointPrefix_charge P m row inside]
        simpa only [Nat.add_assoc] using (stored.rows row inside).2.2.2

theorem StoredCache.original_codec {P : Parameters} {E : ℕ} {state : State}
    (stored : StoredCache P E (P.certificate.M+1) state) :
    HeapList state E (encodeList encodeEndpoint P.endpointCache.toList) := by
  rw [←endpointPrefix_original]
  exact stored.heapPrefix

end RootD27.Endpoint
