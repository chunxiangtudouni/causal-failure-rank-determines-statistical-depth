module

public import PaperProofs.Paid.PDROC_MarkedFees_001
public import PaperProofs.Common.ReferenceObservationCost

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u v

theorem paid_runBill_eq_observation_add_correction (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type u}
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World) :
    runActualBill (P.input fee hfee) C.val mode accounting rule sample =
      runObservationBill (P.input fee hfee) C.val mode accounting rule sample +
        P.runActualCorrectionBill fee hfee C mode accounting rule sample := by
  have ho : Monotone (fun n => (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.observationBill
      (P.input fee hfee).fees) := by
    intro n m hnm
    apply Finset.sum_le_sum
    intro stage _
    exact mul_le_mul_right (ENat.toENNReal_mono
      (run_reviews_mono (P.input fee hfee) C.val mode accounting rule hl sample stage hnm)) _
  have hc : Monotone (fun n => (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.correctionBill
      (P.input fee hfee).fees) := by
    intro n m hnm
    dsimp only
    rw [paid_correctionBill_eq_count, paid_correctionBill_eq_count]
    apply mul_le_mul' _ le_rfl
    exact_mod_cast run_executionCount_mono (P.input fee hfee) C.val mode accounting rule sample hnm
  exact (ENNReal.iSup_add_iSup_of_monotone ho hc).symm

theorem paid_expectedBill_eq_observation_add_correction (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type u} [MeasurableSpace Seed]
    (policy : Policy (P.input fee hfee) C.val mode accounting Seed) (ν : Measure Seed) :
    expectedBill (P.input fee hfee) C.val mode accounting policy.rule ν =
      expectedObservationBill (P.input fee hfee) C.val mode accounting policy.rule ν +
        P.expectedActualCorrectionBill fee hfee C mode accounting policy.rule ν := by
  unfold expectedBill
  simp_rw [paid_runBill_eq_observation_add_correction P fee hfee C mode accounting policy.rule policy.legal]
  exact lintegral_add_left
    (measurable_runObservationBill (P.input fee hfee) C.val mode accounting policy.rule policy.measurable_rule) _

theorem expectedActualCorrectionBill_eq_of_law (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (source : Policy (P.input fee hfee) C.val .uncapped accounting SourceSeed) (νsource : Measure SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed) (νactual : Measure SimSeed)
    (hlaw : P.actualCorrectionBillLaw fee hfee C .uncapped accounting actual.rule νactual =
      P.actualCorrectionBillLaw fee hfee C .uncapped accounting source.rule νsource) :
    P.expectedActualCorrectionBill fee hfee C .uncapped accounting actual.rule νactual =
      P.expectedActualCorrectionBill fee hfee C .uncapped accounting source.rule νsource := by
  have ha := lintegral_map (μ := (P.input fee hfee).seededWorldLaw νactual) measurable_id
    (P.measurable_runActualCorrectionBill fee hfee C .uncapped accounting actual.rule actual.measurable_rule)
  have hs := lintegral_map (μ := (P.input fee hfee).seededWorldLaw νsource) measurable_id
    (P.measurable_runActualCorrectionBill fee hfee C .uncapped accounting source.rule source.measurable_rule)
  change (∫⁻ bill : ℝ≥0∞, bill ∂P.actualCorrectionBillLaw fee hfee C .uncapped accounting actual.rule νactual) =
    P.expectedActualCorrectionBill fee hfee C .uncapped accounting actual.rule νactual at ha
  change (∫⁻ bill : ℝ≥0∞, bill ∂P.actualCorrectionBillLaw fee hfee C .uncapped accounting source.rule νsource) =
    P.expectedActualCorrectionBill fee hfee C .uncapped accounting source.rule νsource at hs
  rw [← ha, ← hs, hlaw]

/-- D06's final all-failure objective comparison is automatic from its three
actual outputs: observation domination, correction FEE LAW equality, and risk
equality. Both the objective and every infinity case use the original bill. -/
theorem paidPenaltyObjective_le_of_actual_components (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (source : Policy (P.input fee hfee) C.val .uncapped accounting SourceSeed) (νsource : Measure SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed) (νactual : Measure SimSeed)
    (hobs : expectedObservationBill (P.input fee hfee) C.val .uncapped accounting actual.rule νactual ≤
      expectedObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule νsource)
    (hlaw : P.actualCorrectionBillLaw fee hfee C .uncapped accounting actual.rule νactual =
      P.actualCorrectionBillLaw fee hfee C .uncapped accounting source.rule νsource)
    (hrisk : risk (P.input fee hfee) C.val .uncapped accounting actual.rule νactual =
      risk (P.input fee hfee) C.val .uncapped accounting source.rule νsource)
    (penalty : ℝ≥0∞) :
    paidPenaltyObjective (P.input fee hfee) C.val accounting actual.rule νactual penalty ≤
      paidPenaltyObjective (P.input fee hfee) C.val accounting source.rule νsource penalty := by
  unfold paidPenaltyObjective
  rw [paid_expectedBill_eq_observation_add_correction P fee hfee C .uncapped accounting actual νactual,
    paid_expectedBill_eq_observation_add_correction P fee hfee C .uncapped accounting source νsource,
    expectedActualCorrectionBill_eq_of_law P fee hfee C accounting source νsource actual νactual hlaw, hrisk]
  exact add_le_add (add_le_add hobs le_rfl) le_rfl

end PDROC
