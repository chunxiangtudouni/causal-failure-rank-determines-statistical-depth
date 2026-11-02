module

public import PaperProofs.Star.PStar_UniversalReviewBound_036
public import PaperProofs.Star.PStar_CountStageBill_032

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarUniversalStageBill037

open Common Common.Native Parameters PStarLR PStarLocalWorld012 PStarCurrentLegality006 PStarUniversalReviewBound036
open scoped ENNReal BigOperators

noncomputable def universalHeadCharge (P : PaperProofs.Star.Parameters) (r : ℝ) (world : (P.input .universalFirst).World) : ℝ≥0∞ :=
  localCharge (P.input .universalFirst) (universalStage P.tools .universalFirst)
    (P.channel.symmetricHittingTest (realTargetIndex P.channel (starTargetReal r 1))) (world (universalStage P.tools .universalFirst))

noncomputable def universalCriticalCharge (P : PaperProofs.Star.Parameters) (r : ℝ) (world : (P.input .universalFirst).World) : ℝ≥0∞ :=
  localCharge (P.input .universalFirst) (singletonStage P.tools .universalFirst P.firstTool)
    (P.channel.symmetricHittingTest (realTargetIndex P.channel (min (1/4) (r / starTargetReal r 1))))
    (world (singletonStage P.tools .universalFirst P.firstTool))

noncomputable def universalSecondAllowance (P : PaperProofs.Star.Parameters) (r : ℝ)
    (world : (P.input .universalFirst).World) : ℝ≥0∞ := by
  classical
  exact if universalHeadTestError P r world then universalCriticalCharge P r world else 0

set_option backward.isDefEq.respectTransparency.types false in
theorem stageBill_le_of_counts (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (stage : (starInstance P.tools order).Stage) (target : ℝ)
    (counts : ∀ clock, (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) sample clock).ledger.reviews stage ≤
        realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 stage)) :
    runStageObservationBill (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) stage sample ≤
      localCharge (P.input order) stage (P.channel.symmetricHittingTest (realTargetIndex P.channel target)) (sample.2 stage) := by
  unfold runStageObservationBill
  apply iSup_le
  intro clock
  have chargeEq : P.channel.experiment.observationCharge
      (realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 stage)) =
      ENNReal.ofReal ((P.input order).fees.observation stage : ℝ) *
        (realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 stage) : ℝ≥0∞) :=
    (P.input order).observationCharge_agrees stage _
  have localEq : localCharge (P.input order) stage (P.channel.symmetricHittingTest (realTargetIndex P.channel target)) (sample.2 stage) =
      P.channel.experiment.observationCharge
        (realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 stage)) := by
    change P.channel.experiment.observationCharge ((P.channel.symmetricHittingTest (realTargetIndex P.channel target)).rule.stop ()
      ((P.input order).reviewAt sample.2 stage)) = _
    exact congrArg P.channel.experiment.observationCharge (realPosteriorStop_eq_hitting P.channel target _).symm
  exact (mul_le_mul_right (ENat.toENNReal_mono (counts clock)) _).trans_eq (chargeEq.symm.trans localEq.symm)

theorem stageBill_eq_zero_of_counts (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (stage : (starInstance P.tools order).Stage)
    (counts : ∀ clock, (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) sample clock).ledger.reviews stage ≤ 0) :
    runStageObservationBill (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) stage sample = 0 := by
  unfold runStageObservationBill
  simp only [le_zero_iff.mp (counts _), ENat.toENNReal_zero, mul_zero, iSup_const]

theorem universalStageBill_le (P : PaperProofs.Star.Parameters) (r : ℝ)
    (C : Contract (starInstance P.tools .universalFirst)) (accounting : NormalAccounting (starInstance P.tools .universalFirst))
    (sample : Unit × (P.input .universalFirst).World) (stage : (starInstance P.tools .universalFirst).Stage) :
    runStageObservationBill (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) stage sample ≤
      (if stage = universalStage P.tools .universalFirst then universalHeadCharge P r sample.2 else 0) +
      (if stage = singletonStage P.tools .universalFirst P.firstTool then universalSecondAllowance P r sample.2 else 0) := by
  classical
  have counts := run_universalReviews_le P r C accounting sample
  by_cases head : stage = universalStage P.tools .universalFirst
  · subst stage
    rw [ite_eq_left rfl, ite_eq_right (Ne.symm (critical_ne_universal P)), add_zero]
    apply stageBill_le_of_counts P .universalFirst .current r C accounting sample _ (starTargetReal r 1)
    intro clock
    simpa only [universalReviewAllowance, ↓reduceIte] using counts clock (universalStage P.tools .universalFirst)
  · rw [ite_eq_right head, zero_add]
    by_cases critical : stage = singletonStage P.tools .universalFirst P.firstTool
    · subst stage
      rw [ite_eq_left rfl]
      by_cases gate : universalHeadTestError P r sample.2
      · rw [universalSecondAllowance, ite_eq_left gate]
        apply stageBill_le_of_counts P .universalFirst .current r C accounting sample _ (min (1/4) (r / starTargetReal r 1))
        intro clock
        simpa [universalReviewAllowance, critical_ne_universal P, gate] using
          counts clock (singletonStage P.tools .universalFirst P.firstTool)
      · rw [universalSecondAllowance, ite_eq_right gate]
        apply le_of_eq
        apply stageBill_eq_zero_of_counts
        intro clock
        simpa only [universalReviewAllowance, ite_eq_right (critical_ne_universal P), gate, and_false, ↓reduceIte] using
          counts clock (singletonStage P.tools .universalFirst P.firstTool)
    · rw [ite_eq_right critical]
      apply le_of_eq
      apply stageBill_eq_zero_of_counts
      intro clock
      have noTest : ¬(stage = singletonStage P.tools .universalFirst P.firstTool ∧ universalHeadTestError P r sample.2) :=
        fun both => critical both.1
      simpa only [universalReviewAllowance, ite_eq_right head, ite_eq_right noTest] using counts clock stage

/-- Full actual observation bill, including failure/nonreturn paths, is
bounded by the real head test plus the head-error-gated critical test. -/
theorem universalObservationBill_le (P : PaperProofs.Star.Parameters) (r : ℝ)
    (C : Contract (starInstance P.tools .universalFirst)) (accounting : NormalAccounting (starInstance P.tools .universalFirst))
    (sample : Unit × (P.input .universalFirst).World) :
    runObservationBill (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) sample ≤
        universalHeadCharge P r sample.2 + universalSecondAllowance P r sample.2 := by
  classical
  rw [runObservationBill_eq_sum_stage (P.input .universalFirst) C .uncapped accounting
    (P.starReferenceRule .universalFirst .current r none) (current_legal_uncapped P .universalFirst r none C accounting)]
  calc
    _ ≤ ∑ stage : (starInstance P.tools .universalFirst).Stage,
        ((if stage = universalStage P.tools .universalFirst then universalHeadCharge P r sample.2 else 0) +
        (if stage = singletonStage P.tools .universalFirst P.firstTool then universalSecondAllowance P r sample.2 else 0)) :=
      Finset.sum_le_sum (fun stage _member => universalStageBill_le P r C accounting sample stage)
    _ = _ := by rw [Finset.sum_add_distrib]; simp

end PaperProofs.Star.PStarUniversalStageBill037
