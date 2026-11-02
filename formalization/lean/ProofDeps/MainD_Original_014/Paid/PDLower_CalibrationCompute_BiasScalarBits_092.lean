module

public import Paid.PDLower_CalibrationCompute_PostRowScalarBits_085

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

open PaperProofs.Paid.Parameters

namespace PDLower.CalibrationCompute

theorem bias_scalar_encodingBits (gamma : ℚ) (Lgamma : ℕ) (bounded : ratEncodingBits gamma≤Lgamma) :
    ratEncodingBits (1/2-gamma)≤4*(Lgamma+2) ∧ ratEncodingBits (1/2+gamma)≤4*(Lgamma+2) := by
  have subtract := half_sub_scalar_encodingBits gamma Lgamma bounded
  have half : ratEncodingBits (1/2 : ℚ)=4 := by
    norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have add := PDROC.DataBits.ratEncodingBits_add_le (1/2 : ℚ) gamma
  rw [half] at add
  omega

end PDLower.CalibrationCompute
