module

public import PaperProofs.Star.PStar_CountTestErrors_023
public import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCountErrorProbability024

open Common Common.Native Parameters MeasureTheory PStarLR PStarLocalWorld012
  PStarStageProduct011 PStarCountProbability019
open scoped BigOperators ENNReal

noncomputable def countErrorEvent (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ) :
    Set (P.input order).World :=
  {world | ∀ stage : (starInstance P.tools order).Stage,
    (P.channel.symmetricHittingTest (realTargetIndex P.channel (stageTarget P r stage.val))).rule.decision ()
      (world stage).2 ≠ (world stage).1}

set_option backward.isDefEq.respectTransparency.types false in
theorem measurableSet_countErrorEvent (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ) :
    MeasurableSet (countErrorEvent P order r) := by
  have eventEq : countErrorEvent P order r = ⋂ stage : (starInstance P.tools order).Stage,
      {world : (P.input order).World |
        (P.channel.symmetricHittingTest (realTargetIndex P.channel (stageTarget P r stage.val))).rule.decision ()
          (world stage).2 ≠ (world stage).1} := by
    ext world
    simp only [countErrorEvent, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [eventEq]
  apply MeasurableSet.iInter
  intro stage
  exact (measurableSet_eq_fun
    ((P.channel.symmetricHittingTest _).measurable_decision.comp
      (measurable_const.prodMk (measurable_pi_apply stage).snd))
    (measurable_pi_apply stage).fst).compl

set_option backward.isDefEq.respectTransparency.types false in
theorem countErrorEvent_probability_le (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1 / 4) :
    (P.input order).worldLaw (countErrorEvent P order r) ≤ ENNReal.ofReal r := by
  classical
  let error : ∀ stage : (starInstance P.tools order).Stage, (P.input order).StageSample stage → ℝ≥0∞ :=
    fun stage => localError (P.input order) stage
      (P.channel.symmetricHittingTest (realTargetIndex P.channel (stageTarget P r stage.val)))
  have measurableError : ∀ stage, Measurable (error stage) := fun stage => measurable_localError _ _ _
  have indicatorEq (world : (P.input order).World) :
      (countErrorEvent P order r).indicator (fun _ => (1 : ℝ≥0∞)) world =
        ∏ stage : (starInstance P.tools order).Stage, error stage (world stage) := by
    by_cases all : world ∈ countErrorEvent P order r
    · rw [Set.indicator_of_mem all]
      symm
      apply Finset.prod_eq_one
      intro stage _member
      exact ite_eq_left (all stage)
    · rw [Set.indicator_of_notMem all]
      change ¬∀ stage : (starInstance P.tools order).Stage,
        (P.channel.symmetricHittingTest (realTargetIndex P.channel (stageTarget P r stage.val))).rule.decision ()
          (world stage).2 ≠ (world stage).1 at all
      obtain ⟨stage, correct⟩ := not_forall.mp all
      exact (Finset.prod_eq_zero (Finset.mem_univ stage) (show error stage (world stage) = 0 from ite_eq_right correct)).symm
  have measureIntegral : (P.input order).worldLaw (countErrorEvent P order r) =
      ∫⁻ world : (P.input order).World,
        ∏ stage : (starInstance P.tools order).Stage, error stage (world stage) ∂(P.input order).worldLaw := by
    rw [← lintegral_indicator_one (measurableSet_countErrorEvent P order r)]
    exact lintegral_congr indicatorEq
  rw [measureIntegral]
  have productBound := lintegral_stageProduct_le (P.input order) Finset.univ error measurableError
    (fun stage => ENNReal.ofReal (stageTarget P r stage.val)) (by
      intro stage _member
      have bounds := stageTarget_bounds P r positive quarter stage.val
      exact realTarget_localError_le P order stage _ bounds.1 (by linarith))
  have reindex : (∏ stage : (starInstance P.tools order).Stage, ENNReal.ofReal (stageTarget P r stage.val)) =
      prefixWeight P r (P.tools+1) := by
    calc
      _ = ∏ stage : Fin (P.tools+1), ENNReal.ofReal (stageTarget P r stage.val) :=
        Fintype.prod_equiv (stageEquiv P.tools order) _ _ (fun _ => rfl)
      _ = _ := (Finset.prod_range (fun stage => ENNReal.ofReal (stageTarget P r stage))).symm
  exact productBound.trans (reindex.le.trans (fullErrorProduct_le P r positive quarter))

theorem countErrorEvent_seeded_le (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1 / 4) :
    (P.input order).seededWorldLaw (Measure.dirac ())
      {sample : Unit × (P.input order).World | sample.2 ∈ countErrorEvent P order r} ≤ ENNReal.ofReal r := by
  have rectangle : {sample : Unit × (P.input order).World | sample.2 ∈ countErrorEvent P order r} =
      Set.univ ×ˢ countErrorEvent P order r := by ext sample; simp
  rw [rectangle, StatisticalInput.seededWorldLaw, Measure.prod_prod]
  simpa only [measure_univ, one_mul] using countErrorEvent_probability_le P order r positive quarter

end PaperProofs.Star.PStarCountErrorProbability024
