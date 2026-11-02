module

public import PaperProofs.Paid.PDROC_DataBits_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

theorem endpointCache_bits_le (P : Parameters) (fee : ℚ) (L : ℕ)
    (hL : P.MenuEncodingBound fee L) :
    (P.endpointCache.toList.map (fun e => ratEncodingBits e.error + ratEncodingBits e.charge)).sum ≤
      (P.certificate.M+1)*(2*L) := by
  have hb := list_map_sum_bound P.endpointCache.toList
    (fun e => ratEncodingBits e.error + ratEncodingBits e.charge) (2*L) (by
      intro endpoint he
      have herr : endpoint.error ∈ P.menuScalars fee :=
        List.mem_append_left _ (List.mem_flatMap.mpr ⟨endpoint, he, by simp⟩)
      have hcharge : endpoint.charge ∈ P.menuScalars fee :=
        List.mem_append_left _ (List.mem_flatMap.mpr ⟨endpoint, he, by simp⟩)
      have h1 := hL.2 endpoint.error herr
      have h2 := hL.2 endpoint.charge hcharge
      omega)
  simpa only [endpointCache, Array.toList_ofFn, List.length_ofFn] using hb

theorem calibrationCache_bits_le (P : Parameters) :
    ((P.calibrationWeightCache P.endpointCache).toList.map
      (fun e => ratEncodingBits e.error + ratEncodingBits e.weight)).sum ≤
      (P.certificate.M+1)*(512*(P.certificate.Q+1)*(ratEncodingBits P.certificate.gamma+2)) := by
  have hb := list_map_sum_bound (P.calibrationWeightCache P.endpointCache).toList
    (fun e => ratEncodingBits e.error + ratEncodingBits e.weight)
    (512*(P.certificate.Q+1)*(ratEncodingBits P.certificate.gamma+2)) (by
      intro calibration he
      have hm : ∃ m : Fin (P.certificate.M+1),
          (let q := P.cachedCappedError m.val
           ({error := q, weight := (1/2-(P.cachedEndpoint P.endpointCache m.val).error)/(1/2-q)} : CalibrationConstant)) = calibration := by
        simpa only [calibrationWeightCache, Array.toList_ofFn, List.mem_ofFn] using he
      obtain ⟨m, rfl⟩ := hm
      have hq := cachedCappedError_encodingBits_le P (ratEncodingBits P.certificate.gamma) (le_refl _) m.val
      have hw := calibrationWeight_encodingBits_le P (ratEncodingBits P.certificate.gamma) (le_refl _) m.val (by omega)
      have hw' : ratEncodingBits ((1/2-(P.cachedEndpoint P.endpointCache m.val).error)/
          (1/2-P.cachedCappedError m.val)) ≤
          256*(P.certificate.Q+1)*(ratEncodingBits P.certificate.gamma+2) := by
        simpa only [cachedEndpoint_eq, endpointConstant, cachedCappedError_eq, calibrationWeight] using hw
      dsimp only
      nlinarith)
  simpa only [calibrationWeightCache, Array.toList_ofFn, List.length_ofFn] using hb

def numericalSizeBound (P : Parameters) (fee : ℚ) : ℕ :=
  P.certificate.t0 + P.certificate.M + P.certificate.Q + P.bisectionBudget fee +
    (P.certificate.M+1)*(2*menuEncodingSize P fee) +
    (P.certificate.M+1)*(512*(P.certificate.Q+1)*(ratEncodingBits P.certificate.gamma+2)) +
    (1+2*searchSolutionSizeBound P (menuEncodingSize P fee) (P.bisectionBudget fee))

theorem numericalSize_le_bound (P : Parameters) (fee : ℚ) :
    P.numericalSize fee ≤ numericalSizeBound P fee := by
  have hL := menuEncodingSize_bound P fee
  have he := endpointCache_bits_le P fee (menuEncodingSize P fee) hL
  have hc := calibrationCache_bits_le P
  have hs := cachedMultiplierSearch_bits P fee (menuEncodingSize P fee) (P.bisectionBudget fee) hL
  unfold numericalSize buildCachedFrontend frontendBits
  dsimp only
  dsimp only [numericalSizeBound]
  omega

end PDROC.DataBits
