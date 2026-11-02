module

public import PaperProofs.Star.PDROC_StarLRHead_003
public import PaperProofs.Star.PDROC_StarLRHead_005
public import PaperProofs.Star.PStarLR_OriginalLegality_015

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarLRHead

theorem original_runObservationBill_eq (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (late : C.IsLateRetained)
    (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) :
    runObservationBill (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample =
      P.channel.experiment.observationCharge (realPosteriorStop P.channel.experiment r
        ((P.input order).reviewAt sample.2 (firstStage P.tools order))) :=
  reference_runObservationBill_eq P order r C accounting
    (PStarLR.retained_legal_uncapped P order .lateRetained (by decide) r none C
      late.2.1 late.2.2 accounting) sample

theorem original_expectedObservationBill_le (P : PaperProofs.Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (late : C.IsLateRetained)
    (accounting : NormalAccounting (starInstance P.tools order)) {r : ℝ}
    (hr : 0 < r) (hrquarter : r ≤ 1/4) :
    expectedObservationBill (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none (Seed := Unit)) (Measure.dirac ()) ≤
      ENNReal.ofReal (P.channel.a * (Real.log (1/r) + P.channel.h)) := by
  have law : expectedObservationBill (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none (Seed := Unit)) (Measure.dirac ()) =
      P.channel.experiment.bayesObservationCharge (Measure.dirac ())
        (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel r)) := by
    unfold expectedObservationBill
    calc
      _ = ∫⁻ sample : Unit × (P.input order).World,
          P.channel.experiment.observationCharge (realPosteriorStop P.channel.experiment r
            ((P.input order).reviewAt sample.2 (firstStage P.tools order)))
            ∂(P.input order).seededWorldLaw (Measure.dirac ()) := by
        apply lintegral_congr
        intro sample
        exact original_runObservationBill_eq P order r C late accounting sample
      _ = _ := reference_head_charge_world_law P order r
  apply law.le.trans
  unfold PaperProofs.Statistics.BinaryExperiment.bayesObservationCharge
  calc
    _ ≤ ∑ truth : Bool, P.channel.experiment.priorMass truth *
        ENNReal.ofReal (P.channel.a * (Real.log (1/r) + P.channel.h)) := by
      apply Finset.sum_le_sum
      intro truth _
      exact mul_le_mul_right
        (PStarLR.realTarget_test_performance P.channel hr (by linarith) truth).2.2 _
    _ = _ := by rw [← Finset.sum_mul, P.channel.experiment.priorMass_sum, one_mul]

end PDROC.StarLRHead
