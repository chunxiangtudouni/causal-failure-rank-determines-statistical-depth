module

public import PaperProofs.Paid.RepresentationClaims
public import PaperProofs.Common.NativeSeed
public import PaperProofs.Paid.PDROC_OverlayInterface_001
public import PaperProofs.Paid.PDROC_OverlayAssembly_001
public import PaperProofs.Paid.PDROC_OverlayScalar_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

/-- D15's original arbitrary-universe policy conclusion follows from the
record-aware D14 witness encoding candidate and its two scalar budgets. This assembly lemma does
not assert that the D14 construction has already been proved. -/
theorem paidOverlayPolicy_of_recordAwareCoupling
    (P : Parameters) (hrep : OverlayDraft.VirtualErrorCouplingClaims.{u} P)
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

/-- The original D15 policy conclusion, with D13 discharged and only the
record-aware original-text D14 construction left as an explicit premise. -/
theorem paidOverlayPolicy_of_d14_recordAware (P : Parameters)
    (hrep : OverlayDraft.VirtualErrorCouplingClaims.{u} P)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) :
    P.PaidOverlayPolicy.{u} C accounting fee hfee :=
  paidOverlayPolicy_of_recordAwareCoupling P hrep fee hfee C accounting
    (overlayIncrement_le P fee hfee)

/-- No change to the original D15 full-policy infimum or risk comparator.
The only outstanding hypothesis is the complete D14 construction. -/
theorem paidOverlayValue_of_d14_recordAware (P : Parameters)
    (hrep : OverlayDraft.VirtualErrorCouplingClaims.{0} P)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) :
    P.PaidOverlayValue C accounting fee hfee :=
  paidOverlayValue_of_policy P fee hfee C accounting
    (paidOverlayPolicy_of_d14_recordAware P hrep fee hfee C accounting)

end PDROC
