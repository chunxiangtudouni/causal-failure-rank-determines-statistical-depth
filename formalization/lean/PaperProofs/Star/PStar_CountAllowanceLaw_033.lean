module

public import PaperProofs.Star.PStar_CountStageBill_032

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCountAllowanceLaw033

open Common Common.Native Parameters MeasureTheory PStarLR PStarLocalWorld012 PStarStageProduct011
  PStarCountProbability019 PStarCountReviewBound031 PStarCountStageBill032
open scoped BigOperators ENNReal

noncomputable def countLocalError (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (stage : (starInstance P.tools order).Stage) : (P.input order).StageSample stage → ℝ≥0∞ :=
  localError (P.input order) stage (P.channel.symmetricHittingTest (realTargetIndex P.channel (stageTarget P r stage.val)))

noncomputable def countLocalCharge (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (stage : (starInstance P.tools order).Stage) : (P.input order).StageSample stage → ℝ≥0∞ :=
  localCharge (P.input order) stage (P.channel.symmetricHittingTest (realTargetIndex P.channel (stageTarget P r stage.val)))

theorem measurable_countLocalError (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (stage : (starInstance P.tools order).Stage) : Measurable (countLocalError P order r stage) :=
  measurable_localError _ _ _

theorem measurable_countLocalCharge (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (stage : (starInstance P.tools order).Stage) : Measurable (countLocalCharge P order r stage) :=
  measurable_localCharge _ _ _

set_option backward.isDefEq.respectTransparency.types false in
theorem allowance_eq_errorProduct (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (world : (P.input order).World) (stage : (starInstance P.tools order).Stage) :
    countStageAllowance P order r world stage =
      (∏ earlier ∈ Finset.univ.filter (fun earlier : (starInstance P.tools order).Stage => earlier.val < stage.val),
        countLocalError P order r earlier (world earlier)) * countLocalCharge P order r stage (world stage) := by
  classical
  by_cases gate : pastTestErrorGate P order r world stage
  · have productOne : (∏ earlier ∈ Finset.univ.filter (fun earlier : (starInstance P.tools order).Stage => earlier.val < stage.val),
        countLocalError P order r earlier (world earlier)) = 1 := by
      apply Finset.prod_eq_one
      intro earlier member
      exact ite_eq_left (gate earlier (Finset.mem_filter.mp member).2)
    rw [countStageAllowance, ite_eq_left gate, productOne, one_mul]
    rfl
  · have missing : ¬∀ earlier : (starInstance P.tools order).Stage, earlier.val < stage.val →
        (P.channel.symmetricHittingTest (realTargetIndex P.channel (stageTarget P r earlier.val))).rule.decision ()
          ((P.input order).reviewAt world earlier) ≠ (P.input order).truthAt world earlier := gate
    obtain ⟨earlier, missing⟩ := not_forall.mp missing
    obtain ⟨before, correct⟩ := not_imp.mp missing
    have zero : countLocalError P order r earlier (world earlier) = 0 := ite_eq_right correct
    have productZero : (∏ previous ∈ Finset.univ.filter (fun previous : (starInstance P.tools order).Stage => previous.val < stage.val),
        countLocalError P order r previous (world previous)) = 0 := Finset.prod_eq_zero
      (Finset.mem_filter.mpr ⟨Finset.mem_univ earlier, before⟩) zero
    rw [countStageAllowance, ite_eq_right gate, productZero, zero_mul]

theorem measurable_countStageAllowance (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (stage : (starInstance P.tools order).Stage) :
    Measurable (fun world : (P.input order).World => countStageAllowance P order r world stage) := by
  have identity : (fun world : (P.input order).World => countStageAllowance P order r world stage) =
      (fun world => (∏ earlier ∈ Finset.univ.filter (fun earlier : (starInstance P.tools order).Stage => earlier.val < stage.val),
        countLocalError P order r earlier (world earlier)) * countLocalCharge P order r stage (world stage)) := by
    funext world
    exact allowance_eq_errorProduct P order r world stage
  rw [identity]
  apply Measurable.mul
  · exact Finset.measurable_prod _ (fun earlier _member =>
      (measurable_countLocalError P order r earlier).comp (measurable_pi_apply earlier))
  · exact (measurable_countLocalCharge P order r stage).comp (measurable_pi_apply stage)

theorem lintegral_world_seededUnit {I : Instance} (input : StatisticalInput I)
    (f : input.World → ℝ≥0∞) (measurable : Measurable f) :
    (∫⁻ sample : Unit × input.World, f sample.2 ∂input.seededWorldLaw (Measure.dirac ())) =
      ∫⁻ world, f world ∂input.worldLaw := by
  rw [StatisticalInput.seededWorldLaw]
  calc
    _ = ∫⁻ _seed : Unit, ∫⁻ world, f world ∂input.worldLaw ∂Measure.dirac () :=
      lintegral_prod (fun sample : Unit × input.World => f sample.2) (measurable.comp measurable_snd).aemeasurable
    _ = _ := by simp only [lintegral_const, measure_univ, mul_one]

theorem pastProduct_eq_prefixWeight (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (stage : (starInstance P.tools order).Stage) :
    (∏ earlier ∈ Finset.univ.filter (fun earlier : (starInstance P.tools order).Stage => earlier.val < stage.val),
      ENNReal.ofReal (stageTarget P r earlier.val)) = prefixWeight P r stage.val := by
  classical
  unfold prefixWeight
  apply Finset.prod_bij (fun earlier _member => earlier.val)
  · intro earlier member
    exact Finset.mem_range.mpr (Finset.mem_filter.mp member).2
  · intro left _left right _right equal
    exact Fin.ext equal
  · intro earlier member
    have before := Finset.mem_range.mp member
    refine ⟨⟨earlier, before.trans stage.isLt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, before⟩, rfl⟩
  · intro earlier _member
    rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem lintegral_countAllowance_le (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1/4) (stage : (starInstance P.tools order).Stage) :
    (∫⁻ world : (P.input order).World, countStageAllowance P order r world stage ∂(P.input order).worldLaw) ≤
      prefixWeight P r stage.val * ENNReal.ofReal (P.channel.a * (Real.log (1 / stageTarget P r stage.val) + P.channel.h)) := by
  classical
  let past := Finset.univ.filter (fun earlier : (starInstance P.tools order).Stage => earlier.val < stage.val)
  have fresh : stage ∉ past := by simp [past]
  have law := lintegral_stageProduct_charge (P.input order) past stage fresh
    (countLocalError P order r) (measurable_countLocalError P order r)
    (countLocalCharge P order r stage) (measurable_countLocalCharge P order r stage)
  have equality : (∫⁻ world : (P.input order).World, countStageAllowance P order r world stage ∂(P.input order).worldLaw) =
      (∏ earlier ∈ past, ∫⁻ localSample, countLocalError P order r earlier localSample ∂(P.input order).stageLaw earlier) *
        ∫⁻ localSample, countLocalCharge P order r stage localSample ∂(P.input order).stageLaw stage := by
    calc
      _ = ∫⁻ world : (P.input order).World, (∏ earlier ∈ past, countLocalError P order r earlier (world earlier)) *
          countLocalCharge P order r stage (world stage) ∂(P.input order).worldLaw :=
        lintegral_congr (fun world => allowance_eq_errorProduct P order r world stage)
      _ = _ := law
  rw [equality]
  have productBound : (∏ earlier ∈ past, ∫⁻ localSample, countLocalError P order r earlier localSample ∂(P.input order).stageLaw earlier) ≤
      ∏ earlier ∈ past, ENNReal.ofReal (stageTarget P r earlier.val) := by
    apply Finset.prod_le_prod
    intro earlier _member
    have bounds := stageTarget_bounds P r positive quarter earlier.val
    exact realTarget_localError_le P order earlier _ bounds.1 (by linarith)
  have bounds := stageTarget_bounds P r positive quarter stage.val
  have chargeBound := realTarget_localCharge_le P order stage _ bounds.1 (by linarith)
  exact (mul_le_mul' productBound chargeBound).trans_eq
    (congrArg (fun weight => weight * ENNReal.ofReal (P.channel.a * (Real.log (1 / stageTarget P r stage.val) + P.channel.h)))
      (pastProduct_eq_prefixWeight P order r stage))

end PaperProofs.Star.PStarCountAllowanceLaw033
