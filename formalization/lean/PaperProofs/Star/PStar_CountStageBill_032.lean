module

public import PaperProofs.Star.PStar_CountReviewBound_031
public import PaperProofs.Common.ReferenceObservationCost

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCountStageBill032

open Common Common.Native Parameters PStarLR PStarLocalWorld012 PStarCountProbability019 PStarCountReviewBound031
open scoped ENNReal

noncomputable def countStageAllowance (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (world : (P.input order).World) (stage : (starInstance P.tools order).Stage) : ℝ≥0∞ := by
  classical
  exact if pastTestErrorGate P order r world stage then
    localCharge (P.input order) stage (P.channel.symmetricHittingTest (realTargetIndex P.channel (stageTarget P r stage.val)))
      (world stage) else 0

set_option backward.isDefEq.respectTransparency.types false in
theorem runStageObservationBill_le_allowance (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (countKind : kind = .earlyRetained ∨ (kind = .current ∧ order = .singletonsFirst))
    (r : ℝ) (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (sample : Unit × (P.input order).World)
    (stage : (starInstance P.tools order).Stage) :
    runStageObservationBill (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) stage sample ≤ countStageAllowance P order r sample.2 stage := by
  classical
  unfold runStageObservationBill
  apply iSup_le
  intro clock
  have counts := run_countReviews_le P order kind countKind r C qualified accounting sample clock stage
  by_cases gate : pastTestErrorGate P order r sample.2 stage
  · rw [countStageAllowance, ite_eq_left gate]
    rw [countReviewAllowance, ite_eq_left gate] at counts
    have chargeEq : P.channel.experiment.observationCharge
        (realPosteriorStop P.channel.experiment (stageTarget P r stage.val) ((P.input order).reviewAt sample.2 stage)) =
        ENNReal.ofReal ((P.input order).fees.observation stage : ℝ) *
          (realPosteriorStop P.channel.experiment (stageTarget P r stage.val) ((P.input order).reviewAt sample.2 stage) : ℝ≥0∞) :=
      (P.input order).observationCharge_agrees stage _
    have localEq : localCharge (P.input order) stage
        (P.channel.symmetricHittingTest (realTargetIndex P.channel (stageTarget P r stage.val))) (sample.2 stage) =
        P.channel.experiment.observationCharge
          (realPosteriorStop P.channel.experiment (stageTarget P r stage.val) ((P.input order).reviewAt sample.2 stage)) := by
      change P.channel.experiment.observationCharge
          ((P.channel.symmetricHittingTest (realTargetIndex P.channel (stageTarget P r stage.val))).rule.stop ()
            ((P.input order).reviewAt sample.2 stage)) = _
      exact congrArg P.channel.experiment.observationCharge
        (realPosteriorStop_eq_hitting P.channel (stageTarget P r stage.val) _).symm
    calc
      _ ≤ ENNReal.ofReal ((P.input order).fees.observation stage : ℝ) *
          (realPosteriorStop P.channel.experiment (stageTarget P r stage.val) ((P.input order).reviewAt sample.2 stage) : ℝ≥0∞) :=
        mul_le_mul_right (ENat.toENNReal_mono counts) _
      _ = _ := chargeEq.symm.trans localEq.symm
  · rw [countStageAllowance, ite_eq_right gate]
    rw [countReviewAllowance, ite_eq_right gate] at counts
    have zero := le_zero_iff.mp counts
    rw [zero, ENat.toENNReal_zero, mul_zero]

end PaperProofs.Star.PStarCountStageBill032
