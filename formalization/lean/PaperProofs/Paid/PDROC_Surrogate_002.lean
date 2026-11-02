module

public import PaperProofs.Paid.PDROC_Surrogate_001
public import PaperProofs.Paid.RepresentationClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Statistics.BinarySymmetric

namespace PDROC

/-- Choosing the more accurate of two target errors costs at most the sum
of their original extended ROC prices, including infinite prices. -/
theorem rocPrice_min_le_add (P : Parameters) (p q : ℝ) :
    P.rocPrice (min p q) ≤ P.rocPrice p + P.rocPrice q := by
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq]
    exact le_self_add
  · rw [min_eq_right hqp]
    exact le_add_self

/-- The original auxiliary endpoint record retains its exact independent ROC price. -/
theorem recordPosterior_rocPrice (P : PaperProofs.Paid.Parameters)
    (record : PaperProofs.Paid.AuxiliaryRecord) :
    P.binarySymmetric.rocPrice (P.recordPosteriorError record) =
      ENNReal.ofReal (P.binarySymmetric.endpointCharge record.level : ℝ) :=
  P.binarySymmetric.rocPrice_endpoint record.level

/-- Pointwise scalar observation budget for the true D14 local target. -/
theorem overlayRecord_rocPrice_le (P : PaperProofs.Paid.Parameters) (fee : ℚ)
    (record : PaperProofs.Paid.AuxiliaryRecord) :
    P.binarySymmetric.rocPrice (P.overlayRecordTarget fee record) ≤
      ENNReal.ofReal (P.binarySymmetric.endpointCharge record.level : ℝ) +
        P.binarySymmetric.rocPrice (P.overlayError fee) := by
  have h := rocPrice_min_le_add P.binarySymmetric (P.recordPosteriorError record) (P.overlayError fee)
  rwa [recordPosterior_rocPrice] at h

/-- The actual target error never exceeds the original fee-dependent error budget. -/
theorem overlayRecordTarget_le_overlayError (P : PaperProofs.Paid.Parameters) (fee : ℚ)
    (record : PaperProofs.Paid.AuxiliaryRecord) :
    P.overlayRecordTarget fee record ≤ P.overlayError fee :=
  min_le_right _ _

/-- Per-record actual correction amount, before summing stages. -/
theorem overlayRecord_fee_error_le (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : PaperProofs.Paid.AuxiliaryRecord) :
    ENNReal.ofReal ((fee : ℝ) * P.overlayRecordTarget fee record) ≤
      ENNReal.ofReal ((fee : ℝ) * P.overlayError fee) := by
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (overlayRecordTarget_le_overlayError P fee record)
    (by exact_mod_cast hfee)

end PDROC
