module

public import PaperProofs.Paid.PDROC_OverlayLaw_001
public import PaperProofs.Paid.PDROC_OverlaySimulator_020
public import PaperProofs.Paid.PDROC_FirstFailureFinite_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

/-- Normalize every original mode using the completed D06 theorem, then
insert the concrete record-aware controller. This is conditional assembly:
the complete concrete VirtualOverlayRepresentation still has to be proved. -/
theorem virtualErrorCouplingClaims_of_concreteOverlay (P : Parameters)
    (hnative : ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
      (accounting : NormalAccounting P.sharedInstance) (Seed : Type u) (ms : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := ms
      ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
        letI : IsProbabilityMeasure ν := hν
        ∀ source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed,
          expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤ →
          OverlayDraft.VirtualOverlayRepresentation P fee hfee C accounting ν (overlaySeedLaw P fee hfee ν)
            source (overlayPolicy P fee hfee C accounting source) (overlayData P source.rule)) :
    OverlayDraft.VirtualErrorCouplingClaims.{u} P := by
  intro fee hfee C accounting mode Seed ms ν hν original hfinite
  let : MeasurableSpace Seed := ms
  let : IsProbabilityMeasure ν := hν
  obtain ⟨stopped, hdom, hstopbill, _hstopreturns, _hstopobj⟩ :=
    finiteCost_firstFailureNormalization P 0 (by norm_num) C mode accounting original ν hfinite
  have hstopfinite := ne_top_of_le_ne_top hfinite hstopbill
  have hrep := hnative fee hfee C accounting Seed ms ν hν stopped hstopfinite
  refine ⟨stopped, hdom, OverlaySeed P Seed, inferInstance, overlaySeedLaw P fee hfee ν,
    inferInstance, overlayPolicy P fee hfee C accounting stopped, overlayData P stopped.rule, hrep, ?_⟩
  have hriskEq : risk (P.input 0 (by norm_num)) C.val .uncapped accounting stopped.rule ν =
      risk (P.input 0 (by norm_num)) C.val mode accounting original.rule ν := by
    unfold risk
    congr 1
    ext sample
    exact not_congr (hdom.1 sample)
  have hobs : expectedObservationBill (P.input 0 (by norm_num)) C.val .uncapped accounting stopped.rule ν ≤
      expectedObservationBill (P.input 0 (by norm_num)) C.val mode accounting original.rule ν :=
    lintegral_mono (fun sample => (hdom.2.2.2 sample).1)
  rcases hrep with ⟨_hm, _hcausal, _halign, _hlaw, _hstage, _hpath, _hcells,
    _hreturns, _hsuccess, hrisk, _hobs, _hcorr, hbill⟩
  intro penalty
  unfold paidPenaltyObjective
  calc
    _ ≤ (expectedObservationBill (P.input 0 (by norm_num)) C.val .uncapped accounting stopped.rule ν +
          P.overlayObservationIncrement fee + P.overlayCorrectionAmount fee) +
          penalty * risk (P.input 0 (by norm_num)) C.val .uncapped accounting stopped.rule ν :=
      add_le_add hbill (mul_le_mul_right hrisk penalty)
    _ ≤ _ := by
      rw [hriskEq]
      exact add_le_add (add_le_add (add_le_add hobs le_rfl) le_rfl) le_rfl

end PDROC
