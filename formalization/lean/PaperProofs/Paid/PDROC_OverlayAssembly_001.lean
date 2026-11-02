module

public import PaperProofs.Paid.RepresentationClaims
public import PaperProofs.Common.NativeSeed

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

/-- D15's original arbitrary-universe policy conclusion follows from the
original D14 witness and its two scalar budgets. This assembly lemma does
not assert that the D14 construction has already been proved. -/
theorem paidOverlayPolicy_of_virtualErrorCoupling
    (P : Parameters) (hrep : P.VirtualErrorCouplingClaims.{u})
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (hbudget : P.overlayObservationIncrement fee + P.overlayCorrectionAmount fee ≤
      (17 / 2 : ℝ≥0∞) * P.feeScale fee) :
    P.PaidOverlayPolicy.{u} C accounting fee hfee := by
  intro mode Seed ms ν hν original hfinite
  let : MeasurableSpace Seed := ms
  let : IsProbabilityMeasure ν := hν
  obtain ⟨stopped, hstop, SimSeed, msim, νs, hνs, actual, data, hboundary, hobj⟩ :=
    hrep fee hfee C accounting mode Seed ms ν hν original hfinite
  let : MeasurableSpace SimSeed := msim
  let : IsProbabilityMeasure νs := hνs
  rcases hboundary with ⟨_hm, _hcausal, _halign, _hlaw, _hstage, _hpath, _hcells,
    _hreturns, _hsuccess, hrisk, _hobs, _hcorr, _hbill⟩
  have hriskeq : risk (P.input 0 (by norm_num)) C.val .uncapped accounting stopped.rule ν =
      risk (P.input 0 (by norm_num)) C.val mode accounting original.rule ν := by
    unfold risk
    congr 1
    ext sample
    exact not_congr (hstop.1 sample)
  have hactual : expectedBill (P.input fee hfee) C.val .uncapped accounting actual.rule νs ≤
      expectedObservationBill (P.input 0 (by norm_num)) C.val mode accounting original.rule ν +
        (17 / 2 : ℝ≥0∞) * P.feeScale fee := by
    have hzero := hobj 0
    simp only [paidPenaltyObjective, zero_mul, add_zero] at hzero
    exact hzero.trans (by simpa only [add_assoc] using
      (add_le_add le_rfl hbudget))
  refine ⟨LegalStrategy (P.input fee hfee) C.val .uncapped accounting, inferInstance,
    encodedSeedLaw (P.input fee hfee) C.val .uncapped accounting actual νs,
    inferInstance, strategyPolicy (P.input fee hfee) C.val .uncapped accounting, ?_, ?_⟩
  · rw [risk_encoded_eq, ← hriskeq]
    exact hrisk
  · rw [expectedBill_encoded_eq]
    exact hactual

/-- Passing to the full original infimum uses every safe source policy;
infinite bills are handled directly and no minimizer is required. -/
theorem paidOverlayValue_of_policy
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (hpolicy : P.PaidOverlayPolicy.{0} C accounting fee hfee) :
    P.PaidOverlayValue C accounting fee hfee := by
  change P.uncappedValue C accounting fee hfee ≤
    value (P.input 0 (by norm_num)) C.val .uncapped accounting P.targetRisk +
      9 * P.feeScale fee
  unfold value
  simp only [ENNReal.iInf_add]
  refine le_iInf fun Seed => le_iInf fun ms => ?_
  let : MeasurableSpace Seed := ms
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun original => ?_
  by_cases hf : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting original.val.rule ν ≠ ⊤
  · obtain ⟨Seed', ms', ν', hν', paid, hrisk, hbill⟩ :=
      hpolicy .uncapped Seed ms ν hν original.val hf
    let : MeasurableSpace Seed' := ms'
    let : IsProbabilityMeasure ν' := hν'
    calc
      P.uncappedValue C accounting fee hfee ≤
          expectedBill (P.input fee hfee) C.val .uncapped accounting paid.rule ν' :=
        value_le_policy_any_seed (P.input fee hfee) C.val .uncapped accounting paid ν'
          P.targetRisk (hrisk.trans original.property)
      _ ≤ expectedObservationBill (P.input 0 (by norm_num)) C.val .uncapped accounting original.val.rule ν +
          (17 / 2 : ℝ≥0∞) * P.feeScale fee := hbill
      _ ≤ expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting original.val.rule ν +
          9 * P.feeScale fee := by
        rw [P.free_expectedBill_eq_observation]
        have hcoef : (17 / 2 : ℝ≥0∞) ≤ 9 := by
          rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
          norm_num
        exact add_le_add le_rfl (by gcongr)
  · simp only [not_ne_iff] at hf
    simp only [hf, top_add, le_top]

end PDROC
