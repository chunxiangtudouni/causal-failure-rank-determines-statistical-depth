module

public import PaperProofs.Paid.PDMenu_EndpointNativeWeights_039
public import PaperProofs.Common.NativeBellmanValueUpper

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

/-- The only approximation loss is the chosen epsilon. Infinite costs are
allowed; this is a semiring identity, with no subtracting infinity. -/
theorem paidWeightedNear_sum (observation good bad correct wrong epsilon : ℝ≥0∞)
    (hweights : correct + wrong = 1) :
    observation + correct * (good + epsilon) + wrong * (bad + epsilon) =
      observation + correct * good + wrong * bad + epsilon := by
  calc
    _ = observation + correct * good + wrong * bad + (correct + wrong) * epsilon := by ring
    _ = _ := by rw [hweights, one_mul]

theorem freshEndpoint_weights_sum (P : Parameters) (n k : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (head : (freshInstance n k).Stage) (m : ℕ) :
    ENNReal.ofReal (1 - (P.binarySymmetric.endpointError m : ℝ)) +
      ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ) = 1 := by
  have h := BellmanExpectation.correctMass_add_bayesError (P.freshInput n k fee hfee) head fairGuessLaw
    (freshEndpointTest P n k fee hfee head m)
  rw [freshEndpointTest_correctMass, freshEndpointTest_bayesError] at h
  exact h

end PDMenu

