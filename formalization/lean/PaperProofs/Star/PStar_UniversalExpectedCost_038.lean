module

public import PaperProofs.Star.PStar_UniversalStageBill_037
public import PaperProofs.Star.PStar_CountAllowanceLaw_033
public import PaperProofs.Star.RootStarEnvelope_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarUniversalExpectedCost038

open Common Common.Native Parameters MeasureTheory PStarLR PStarLocalWorld012 PStarStageProduct011
  PStarCountAllowanceLaw033 PStarUniversalReviewBound036 PStarUniversalStageBill037
open scoped ENNReal BigOperators

theorem measurable_universalHeadCharge (P : PaperProofs.Star.Parameters) (r : ℝ) :
    Measurable (universalHeadCharge P r) :=
  (measurable_localCharge _ _ _).comp (measurable_pi_apply (universalStage P.tools .universalFirst))

theorem measurable_universalCriticalCharge (P : PaperProofs.Star.Parameters) (r : ℝ) :
    Measurable (universalCriticalCharge P r) :=
  (measurable_localCharge _ _ _).comp (measurable_pi_apply (singletonStage P.tools .universalFirst P.firstTool))

set_option backward.isDefEq.respectTransparency.types false in
theorem secondAllowance_eq_errorCharge (P : PaperProofs.Star.Parameters) (r : ℝ) (world : (P.input .universalFirst).World) :
    universalSecondAllowance P r world =
      localError (P.input .universalFirst) (universalStage P.tools .universalFirst)
        (P.channel.symmetricHittingTest (realTargetIndex P.channel (starTargetReal r 1)))
        (world (universalStage P.tools .universalFirst)) * universalCriticalCharge P r world := by
  classical
  by_cases gate : universalHeadTestError P r world
  · rw [universalSecondAllowance, ite_eq_left gate]
    have one : localError (P.input .universalFirst) (universalStage P.tools .universalFirst)
        (P.channel.symmetricHittingTest (realTargetIndex P.channel (starTargetReal r 1)))
        (world (universalStage P.tools .universalFirst)) = 1 := ite_eq_left gate
    rw [one, one_mul]
  · rw [universalSecondAllowance, ite_eq_right gate]
    have zero : localError (P.input .universalFirst) (universalStage P.tools .universalFirst)
        (P.channel.symmetricHittingTest (realTargetIndex P.channel (starTargetReal r 1)))
        (world (universalStage P.tools .universalFirst)) = 0 := ite_eq_right gate
    rw [zero, zero_mul]

theorem measurable_universalSecondAllowance (P : PaperProofs.Star.Parameters) (r : ℝ) :
    Measurable (universalSecondAllowance P r) := by
  have identity : universalSecondAllowance P r = fun world : (P.input .universalFirst).World =>
      localError (P.input .universalFirst) (universalStage P.tools .universalFirst)
        (P.channel.symmetricHittingTest (realTargetIndex P.channel (starTargetReal r 1)))
        (world (universalStage P.tools .universalFirst)) * universalCriticalCharge P r world := by
    funext world
    exact secondAllowance_eq_errorCharge P r world
  rw [identity]
  exact ((measurable_localError _ _ _).comp (measurable_pi_apply (universalStage P.tools .universalFirst))).mul
    (measurable_universalCriticalCharge P r)

set_option backward.isDefEq.respectTransparency.types false in
theorem lintegral_universalHeadCharge_le (P : PaperProofs.Star.Parameters) (r : ℝ) :
    (∫⁻ world, universalHeadCharge P r world ∂(P.input .universalFirst).worldLaw) ≤
      ENNReal.ofReal (P.channel.a * (Real.log (1 / starTargetReal r 1) + P.channel.h)) := by
  have law : (∫⁻ world, universalHeadCharge P r world ∂(P.input .universalFirst).worldLaw) =
      ∫⁻ localSample, localCharge (P.input .universalFirst) (universalStage P.tools .universalFirst)
        (P.channel.symmetricHittingTest (realTargetIndex P.channel (starTargetReal r 1))) localSample
        ∂(P.input .universalFirst).stageLaw (universalStage P.tools .universalFirst) := by
    change (∫⁻ world, localCharge (P.input .universalFirst) (universalStage P.tools .universalFirst)
      (P.channel.symmetricHittingTest (realTargetIndex P.channel (starTargetReal r 1)))
      (world (universalStage P.tools .universalFirst)) ∂(P.input .universalFirst).worldLaw) = _
    rw [← lintegral_map (measurable_localCharge _ _ _) (measurable_pi_apply (universalStage P.tools .universalFirst)),
      (P.input .universalFirst).worldLaw_coordinate]
  exact law.le.trans (realTarget_localCharge_le P .universalFirst _ _ (RootStarQuota.starTarget_pos r 1)
    (lt_of_le_of_lt (RootStarQuota.starTarget_le_quarter r 1) (by norm_num)))

set_option backward.isDefEq.respectTransparency.types false in
theorem lintegral_universalSecondAllowance_le (P : PaperProofs.Star.Parameters) (r : ℝ) (positive : 0 < r) :
    (∫⁻ world, universalSecondAllowance P r world ∂(P.input .universalFirst).worldLaw) ≤
      ENNReal.ofReal (starTargetReal r 1) *
        ENNReal.ofReal (P.channel.a * (Real.log (1 / min (1/4) (r / starTargetReal r 1)) + P.channel.h)) := by
  classical
  let errors : ∀ stage : (starInstance P.tools .universalFirst).Stage, (P.input .universalFirst).StageSample stage → ℝ≥0∞ :=
    fun stage => localError (P.input .universalFirst) stage
      (P.channel.symmetricHittingTest (realTargetIndex P.channel (starTargetReal r 1)))
  let charge := localCharge (P.input .universalFirst) (singletonStage P.tools .universalFirst P.firstTool)
    (P.channel.symmetricHittingTest (realTargetIndex P.channel (min (1/4) (r / starTargetReal r 1))))
  have law := lintegral_stageProduct_charge (P.input .universalFirst) {universalStage P.tools .universalFirst}
    (singletonStage P.tools .universalFirst P.firstTool)
    (by simpa only [Finset.mem_singleton] using critical_ne_universal P)
    errors (fun _stage => measurable_localError _ _ _) charge (measurable_localCharge _ _ _)
  simp only [Finset.prod_singleton] at law
  have equality : (∫⁻ world, universalSecondAllowance P r world ∂(P.input .universalFirst).worldLaw) =
      (∫⁻ localSample, errors (universalStage P.tools .universalFirst) localSample
        ∂(P.input .universalFirst).stageLaw (universalStage P.tools .universalFirst)) *
      ∫⁻ localSample, charge localSample ∂(P.input .universalFirst).stageLaw (singletonStage P.tools .universalFirst P.firstTool) := by
    calc
      _ = ∫⁻ world, errors (universalStage P.tools .universalFirst) (world (universalStage P.tools .universalFirst)) *
          charge (world (singletonStage P.tools .universalFirst P.firstTool)) ∂(P.input .universalFirst).worldLaw :=
        lintegral_congr (fun world => secondAllowance_eq_errorCharge P r world)
      _ = _ := law
  rw [equality]
  have hp := RootStarQuota.starTarget_pos r 1
  have hq := RootStarQuota.starTarget_le_quarter r 1
  exact mul_le_mul' (realTarget_localError_le P .universalFirst _ _ hp (by linarith))
    (realTarget_localCharge_le P .universalFirst _ _ (lt_min (by norm_num) (div_pos positive hp))
      (lt_of_le_of_lt (min_le_left _ _) (by norm_num)))

/-- Original C07 expected observation bill of the ACTUAL whole script,
including earlier observations on actual failures and infinite sample paths. -/
theorem universalExpectedObservationBound (P : PaperProofs.Star.Parameters)
    (C : Contract (starInstance P.tools .universalFirst)) (accounting : NormalAccounting (starInstance P.tools .universalFirst))
    (r : ℝ) (positive : 0 < r) :
    expectedObservationBill (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none (Seed := Unit)) (Measure.dirac ()) ≤
        ENNReal.ofReal (P.currentObservationEnvelope r) := by
  classical
  have hp := RootStarQuota.starTarget_pos r 1
  have hq := RootStarQuota.starTarget_le_quarter r 1
  have hsecond : 0 < min (1/4) (r / starTargetReal r 1) := lt_min (by norm_num) (div_pos positive hp)
  have headCostNonneg : 0 ≤ P.channel.a * (Real.log (1 / starTargetReal r 1) + P.channel.h) :=
    mul_nonneg P.channel.a_pos.le (add_nonneg (RootStarEnvelope.log_inverse_nonnegative _ hp hq) P.channel.h_pos.le)
  have secondCostNonneg : 0 ≤ P.channel.a * (Real.log (1 / min (1/4) (r / starTargetReal r 1)) + P.channel.h) :=
    mul_nonneg P.channel.a_pos.le (add_nonneg
      (RootStarEnvelope.log_inverse_nonnegative _ hsecond (min_le_left _ _)) P.channel.h_pos.le)
  unfold expectedObservationBill
  calc
    _ ≤ ∫⁻ sample : Unit × (P.input .universalFirst).World,
        universalHeadCharge P r sample.2 + universalSecondAllowance P r sample.2
        ∂(P.input .universalFirst).seededWorldLaw (Measure.dirac ()) :=
      lintegral_mono (fun sample => universalObservationBill_le P r C accounting sample)
    _ = ∫⁻ world, universalHeadCharge P r world + universalSecondAllowance P r world ∂(P.input .universalFirst).worldLaw :=
      lintegral_world_seededUnit (P.input .universalFirst) _
        ((measurable_universalHeadCharge P r).add (measurable_universalSecondAllowance P r))
    _ = (∫⁻ world, universalHeadCharge P r world ∂(P.input .universalFirst).worldLaw) +
        ∫⁻ world, universalSecondAllowance P r world ∂(P.input .universalFirst).worldLaw :=
      lintegral_add_left (measurable_universalHeadCharge P r) _
    _ ≤ ENNReal.ofReal (P.channel.a * (Real.log (1 / starTargetReal r 1) + P.channel.h)) +
        ENNReal.ofReal (starTargetReal r 1) *
          ENNReal.ofReal (P.channel.a * (Real.log (1 / min (1/4) (r / starTargetReal r 1)) + P.channel.h)) :=
      add_le_add (lintegral_universalHeadCharge_le P r) (lintegral_universalSecondAllowance_le P r positive)
    _ = _ := by
      rw [Parameters.currentObservationEnvelope, mul_assoc, ENNReal.ofReal_add headCostNonneg (mul_nonneg hp.le secondCostNonneg),
        ENNReal.ofReal_mul hp.le]

end PaperProofs.Star.PStarUniversalExpectedCost038
