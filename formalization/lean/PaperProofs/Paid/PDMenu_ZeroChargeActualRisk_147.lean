module

public import PaperProofs.Paid.PDMenu_ZeroChargeBlindRisk_146

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Exact risk of THIS original blind script, transported from the real
Native interpreter and its unchanged seed/world law. -/
theorem zeroCharge_risk (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    risk (P.input fee hfee) C.val .uncapped accounting (P.zeroChargeRule fee)
      (menuSeedLaw P.certificate.stages P.tools) = ENNReal.ofReal (P.zeroChargeRisk fee : ℝ) := by
  rw [zeroChargeRule_eq_blindTable]
  let N := P.certificate.stages
  let K := P.tools
  let table := zeroChargeBlindTable N K fee
  let view := menuSampleFinView P N K fee hfee
  have hview := menuSampleFinView_measurePreserving P N K fee hfee
  have hrecords := PDROC.menuNativeSummaryRefinement P N K table fee hfee C.val C.property accounting
  let failure : Set (MenuAnalysisSeed N × MenuAnalysisWorld P N) :=
    {sample | (menuPathSummary P table N K sample.1 sample.2).failure = true}
  have hfailure : MeasurableSet failure :=
    (measurable_menuPathFailure P table N K) (measurableSet_singleton true)
  change risk (P.freshInput N K fee hfee) C.val .uncapped accounting
    (P.compiledMenuRule N K table) (menuSeedLaw N K) = _
  unfold risk
  calc
    _ = ((P.freshInput N K fee hfee).seededWorldLaw (menuSeedLaw N K)) (view ⁻¹' failure) := by
      apply measure_congr
      filter_upwards [hrecords] with sample hs
      apply propext
      change (¬runSuccess _ _ _ _ _ sample) ↔
        (menuPathSummary P table N K (view sample).1 (view sample).2).failure = true
      rw [hs.2.2]
      cases (menuPathSummary P table N K (view sample).1 (view sample).2).failure <;> decide
    _ = (menuAnalysisLaw P N) failure := hview.measure_preimage hfailure.nullMeasurableSet
    _ = zeroChargeBlindFailureIntegral P N K fee N K :=
      PDROC.MenuExpected.failure_measure_eq_integral P table N K
    _ = ENNReal.ofReal (PDROC.ZeroChargeLower.Binomial.tail N (if fee=0 then K else 0) : ℝ) :=
      zeroChargeBlind_failure_integral P N K fee N le_rfl K le_rfl
    _ = ENNReal.ofReal (P.zeroChargeRisk fee : ℝ) := by
      by_cases hf : fee=0
      · simp only [hf, ite_true, PaperProofs.Paid.Parameters.zeroChargeRisk,
          PDROC.ZeroChargeLower.Binomial.tail_stages_tools, N, K]
      · simp only [hf, ite_false, PaperProofs.Paid.Parameters.zeroChargeRisk,
          PDROC.ZeroChargeLower.Binomial.tail_zero_eq, N]

end PDMenu
