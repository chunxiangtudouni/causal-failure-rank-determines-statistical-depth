module

public import PaperProofs.Star.PStar_UniversalTestErrors_026
public import PaperProofs.Star.PStar_CountErrorProbability_024

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarTwoErrorProbability027

open Common Common.Native Parameters MeasureTheory PStarLR PStarLocalWorld012 PStarStageProduct011
open scoped BigOperators ENNReal

noncomputable def twoErrorEvent (P : PaperProofs.Star.Parameters) (order : Order)
    (left right : (starInstance P.tools order).Stage) (leftTarget rightTarget : ℝ) : Set (P.input order).World :=
  {world | (P.channel.symmetricHittingTest (realTargetIndex P.channel leftTarget)).rule.decision () (world left).2 ≠ (world left).1 ∧
    (P.channel.symmetricHittingTest (realTargetIndex P.channel rightTarget)).rule.decision () (world right).2 ≠ (world right).1}

set_option backward.isDefEq.respectTransparency.types false in
theorem twoErrorEvent_probability_le (P : PaperProofs.Star.Parameters) (order : Order)
    (left right : (starInstance P.tools order).Stage) (distinct : left ≠ right)
    (leftTarget rightTarget : ℝ) (leftPositive : 0 < leftTarget) (leftHalf : leftTarget < 1/2)
    (rightPositive : 0 < rightTarget) (rightHalf : rightTarget < 1/2) :
    (P.input order).worldLaw (twoErrorEvent P order left right leftTarget rightTarget) ≤
      ENNReal.ofReal leftTarget * ENNReal.ofReal rightTarget := by
  classical
  let errors : ∀ stage : (starInstance P.tools order).Stage, (P.input order).StageSample stage → ℝ≥0∞ :=
    fun stage => localError (P.input order) stage (P.channel.symmetricHittingTest (realTargetIndex P.channel leftTarget))
  let otherError := localError (P.input order) right (P.channel.symmetricHittingTest (realTargetIndex P.channel rightTarget))
  have measurableErrors : ∀ stage, Measurable (errors stage) := fun stage => measurable_localError _ _ _
  have measurableOther : Measurable otherError := measurable_localError _ _ _
  have eventMeasurable : MeasurableSet (twoErrorEvent P order left right leftTarget rightTarget) := by
    apply MeasurableSet.inter
    · exact (measurableSet_eq_fun
        ((P.channel.symmetricHittingTest _).measurable_decision.comp (measurable_const.prodMk (measurable_pi_apply left).snd))
        (measurable_pi_apply left).fst).compl
    · exact (measurableSet_eq_fun
        ((P.channel.symmetricHittingTest _).measurable_decision.comp (measurable_const.prodMk (measurable_pi_apply right).snd))
        (measurable_pi_apply right).fst).compl
  have indicatorEq (world : (P.input order).World) :
      (twoErrorEvent P order left right leftTarget rightTarget).indicator (fun _ => (1 : ℝ≥0∞)) world =
        errors left (world left) * otherError (world right) := by
    by_cases leftWrong : (P.channel.symmetricHittingTest (realTargetIndex P.channel leftTarget)).rule.decision ()
        (world left).2 ≠ (world left).1 <;>
      by_cases rightWrong : (P.channel.symmetricHittingTest (realTargetIndex P.channel rightTarget)).rule.decision ()
        (world right).2 ≠ (world right).1 <;>
      simp [twoErrorEvent, errors, otherError, localError, leftWrong, rightWrong]
  have law := lintegral_stageProduct_charge (P.input order) {left} right
    (by simpa only [Finset.mem_singleton] using Ne.symm distinct) errors measurableErrors otherError measurableOther
  simp only [Finset.prod_singleton] at law
  have measureIntegral : (P.input order).worldLaw (twoErrorEvent P order left right leftTarget rightTarget) =
      ∫⁻ world : (P.input order).World, errors left (world left) * otherError (world right) ∂(P.input order).worldLaw := by
    rw [← lintegral_indicator_one eventMeasurable]
    exact lintegral_congr indicatorEq
  rw [measureIntegral, law]
  exact mul_le_mul' (realTarget_localError_le P order left leftTarget leftPositive leftHalf)
    (realTarget_localError_le P order right rightTarget rightPositive rightHalf)

theorem universalErrorEvent_seeded_le (P : PaperProofs.Star.Parameters) (r : ℝ) (positive : 0 < r) :
    (P.input .universalFirst).seededWorldLaw (Measure.dirac ())
      {sample : Unit × (P.input .universalFirst).World | sample.2 ∈
        twoErrorEvent P .universalFirst (universalStage P.tools .universalFirst)
          (singletonStage P.tools .universalFirst P.firstTool) (starTargetReal r 1) (min (1/4) (r / starTargetReal r 1))} ≤
      ENNReal.ofReal r := by
  classical
  let event := twoErrorEvent P .universalFirst (universalStage P.tools .universalFirst)
    (singletonStage P.tools .universalFirst P.firstTool) (starTargetReal r 1) (min (1/4) (r / starTargetReal r 1))
  have rectangle : {sample : Unit × (P.input .universalFirst).World | sample.2 ∈ event} = Set.univ ×ˢ event := by
    ext sample; simp
  change (P.input .universalFirst).seededWorldLaw (Measure.dirac ()) {sample | sample.2 ∈ event} ≤ _
  rw [rectangle, StatisticalInput.seededWorldLaw, Measure.prod_prod]
  simp only [measure_univ, one_mul]
  have targetPositive := RootStarQuota.starTarget_pos r 1
  have targetQuarter := RootStarQuota.starTarget_le_quarter r 1
  have distinct : universalStage P.tools .universalFirst ≠ singletonStage P.tools .universalFirst P.firstTool := by
    intro equal
    have values := congrArg Fin.val equal
    change (0 : ℕ) = 0+1 at values
    omega
  have productBound : starTargetReal r 1 * min (1/4) (r / starTargetReal r 1) ≤ r := by
    calc
      _ ≤ starTargetReal r 1 * (r / starTargetReal r 1) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) targetPositive.le
      _ = r := by field_simp [targetPositive.ne']
  calc
    _ ≤ ENNReal.ofReal (starTargetReal r 1) * ENNReal.ofReal (min (1/4) (r / starTargetReal r 1)) :=
      twoErrorEvent_probability_le P .universalFirst _ _ distinct _ _ targetPositive (by linarith)
        (lt_min (by norm_num) (div_pos positive targetPositive)) (lt_of_le_of_lt (min_le_left _ _) (by norm_num))
    _ = ENNReal.ofReal (starTargetReal r 1 * min (1/4) (r / starTargetReal r 1)) :=
      (ENNReal.ofReal_mul targetPositive.le).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal productBound

end PaperProofs.Star.PStarTwoErrorProbability027
