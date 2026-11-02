module

public import Paid.PDLower_CalibrationCompute_SumValue_022

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- The actual zero-denominator branch matches rational division's
original total value. It introduces no positivity qualification on q. -/
def computedWeight (error q : ℚ) : ℚ :=
  if (1/2-q : ℚ)=0 then 0 else (1/2-error)/(1/2-q)

theorem computedWeight_eq (error q : ℚ) :
    computedWeight error q=(1/2-error)/(1/2-q) := by
  unfold computedWeight
  split_ifs with zero
  · simp only [zero,div_zero]
  · rfl

theorem originalCalibration_pair (P : Parameters) (m : ℕ) (inside : m<P.certificate.M+1) :
    encodeCalibration ((P.calibrationWeightCache P.endpointCache)[m]'(by simpa using inside)) =
      [.rational (P.cachedCappedError m),
       .rational (computedWeight (P.endpointConstant m).error (P.cachedCappedError m))] := by
  simp only [calibrationWeightCache,Array.getElem_ofFn,cachedEndpoint_eq,encodeCalibration,computedWeight_eq]

theorem originalCalibration_error (P : Parameters) (m : ℕ) :
    P.cachedCappedError m=
      rowPrefixSum (P.walkRow (m+1) true P.certificate.Q) (m+1)+
        (P.walkRow (m+1) true P.certificate.Q).getD (m+1) 0*(1/2) :=
  cachedCappedError_eq_prefix P m

end PDLower.CalibrationCompute
