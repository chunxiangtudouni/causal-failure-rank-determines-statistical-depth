module

public import PaperProofs.Paid.PDROC_CalibratedSignature_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open scoped ENNReal

namespace PDROC.CalibratedSignature

/-- Transfer the observation comparison to the complete extended bill.
The correction-fee expectation is transported exactly by the full signature;
neither expected duration nor either bill is assumed finite. -/
theorem expectedBill_le_four_of_signatureLaw
    {SourceSeed TargetSeed : Type*} [MeasurableSpace SourceSeed] [MeasurableSpace TargetSeed]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (actual : Policy (P.input fee hfee) C.val mode accounting TargetSeed) (νactual : Measure TargetSeed)
    (source : Policy (P.input fee hfee) C.val mode accounting SourceSeed) (νsource : Measure SourceSeed)
    (same : P.executionSignatureLaw fee hfee C mode accounting actual.rule νactual =
      P.executionSignatureLaw fee hfee C mode accounting source.rule νsource)
    (observations : expectedObservationBill (P.input fee hfee) C.val mode accounting actual.rule νactual ≤
      4 * expectedObservationBill (P.input fee hfee) C.val mode accounting source.rule νsource) :
    expectedBill (P.input fee hfee) C.val mode accounting actual.rule νactual ≤
      4 * expectedBill (P.input fee hfee) C.val mode accounting source.rule νsource := by
  rw [expectedBill_eq_observation_add_correction P fee hfee C mode accounting actual νactual,
    expectedBill_eq_observation_add_correction P fee hfee C mode accounting source νsource,
    expectedCorrectionBill_eq_of_signatureLaw P fee hfee C mode accounting actual νactual source νsource same]
  have correction : P.expectedActualCorrectionBill fee hfee C mode accounting source.rule νsource ≤
      4 * P.expectedActualCorrectionBill fee hfee C mode accounting source.rule νsource := by
    have four : (1 : ℝ≥0∞) ≤ 4 := by norm_num
    simpa only [one_mul] using
      mul_le_mul' four (le_refl (P.expectedActualCorrectionBill fee hfee C mode accounting source.rule νsource))
  calc
    _ ≤ 4 * expectedObservationBill (P.input fee hfee) C.val mode accounting source.rule νsource +
        4 * P.expectedActualCorrectionBill fee hfee C mode accounting source.rule νsource :=
      add_le_add observations correction
    _ = _ := (mul_add _ _ _).symm

end PDROC.CalibratedSignature
