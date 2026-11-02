module

public import PaperProofs.Retained.PDROC_RetainedEnvelope_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PaperProofs.Retained.PRetObservationEnvelope119

open Common Common.Native Statistics MeasureTheory Filter
open scoped ENNReal Topology

variable {I : Instance}

theorem controllerTarget_price_ratio (j depth : ℕ) (hj : 1 ≤ j) (_hd : 1 ≤ depth)
    (horder : depth ≤ j + 1) (coefficient offset : ℝ) :
    Tendsto (fun risk : ℚ => coefficient *
      (Real.log (1 / (controllerTarget risk j : ℝ)) + offset) /
        iteratedLog depth (1 / (risk : ℝ))) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (coefficient * (if depth = j + 1 then 1 else 0))) := by
  have hden := (iteratedLog_tendsto_atTop depth).comp rationalInverse_tendsto_atTop
  have he := (controllerTarget_log_difference_tendsto j hj).div_atTop hden
  have hm : Tendsto (fun risk : ℚ => iteratedLog (j + 1) (1 / (risk : ℝ)) /
      iteratedLog depth (1 / (risk : ℝ))) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (if depth = j + 1 then 1 else 0)) := by
    by_cases heq : depth = j + 1
    · rw [ite_eq_left heq, ← heq]
      apply (tendsto_const_nhds : Tendsto (fun _ : ℚ => (1 : ℝ)) _ (𝓝 1)).congr'
      filter_upwards [hden.eventually_ne_atTop 0] with risk hn
      exact (div_self hn).symm
    · simpa only [Function.comp_def, heq, ite_false] using
        (iteratedLog_div_tendsto_zero_of_lt depth (j + 1) (by omega)).comp rationalInverse_tendsto_atTop
  have hz : Tendsto (fun risk : ℚ => offset / iteratedLog depth (1 / (risk : ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := tendsto_const_nhds.div_atTop hden
  have hall := ((he.add hm).add hz).const_mul coefficient
  apply (show Tendsto (fun risk : ℚ => coefficient *
      ((Real.log (1 / (controllerTarget risk j : ℝ)) - iteratedLog (j + 1) (1 / (risk : ℝ))) /
          iteratedLog depth (1 / (risk : ℝ)) +
        iteratedLog (j + 1) (1 / (risk : ℝ)) / iteratedLog depth (1 / (risk : ℝ)) +
        offset / iteratedLog depth (1 / (risk : ℝ))))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (coefficient * (if depth = j + 1 then 1 else 0)))
      from by simpa only [Function.comp_def, zero_add, add_zero] using hall).congr'
  exact Filter.Eventually.of_forall (fun risk => by ring)

theorem noTool_price_ratio (coefficient offset : ℝ) :
    Tendsto (fun risk : ℚ => coefficient * (Real.log (1 / ((risk / 2 : ℚ) : ℝ)) + offset) /
      iteratedLog 1 (1 / (risk : ℝ))) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 coefficient) := by
  have hm := rationalRisk_iteratedLog_half_div_tendsto_one 1 le_rfl
  have hz : Tendsto (fun risk : ℚ => offset / iteratedLog 1 (1 / (risk : ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((iteratedLog_tendsto_atTop 1).comp rationalInverse_tendsto_atTop)
  have hall := (hm.add hz).const_mul coefficient
  apply (show Tendsto (fun risk : ℚ => coefficient *
      (iteratedLog 1 (1 / ((risk / 2 : ℚ) : ℝ)) / iteratedLog 1 (1 / (risk : ℝ)) +
        offset / iteratedLog 1 (1 / (risk : ℝ))))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 coefficient)
      from by simpa only [add_zero, mul_one] using hall).congr'
  exact Filter.Eventually.of_forall (fun risk => by simp only [iteratedLog]; ring)

theorem upper_of_ratio (depth : ℕ) (f : ℚ → ℝ) (limit eta : ℝ) (heta : 0 < eta)
    (hf : Tendsto (fun risk : ℚ => f risk / iteratedLog depth (1 / (risk : ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 limit)) :
    ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      f risk ≤ (limit + eta) * iteratedLog depth (1 / (risk : ℝ)) := by
  have hratio := hf.eventually (eventually_lt_nhds (show limit < limit + eta by linarith))
  have hpos := ((iteratedLog_tendsto_atTop depth).comp rationalInverse_tendsto_atTop).eventually_gt_atTop 0
  filter_upwards [hratio, hpos] with risk hr hp
  exact ((div_lt_iff₀ hp).mp hr).le

theorem localPriceReal_le_sharp (input : StatisticalInput I) (stage : I.Stage)
    (kind : ReferenceBudgetCase) (risk target : ℚ) (hv : ReferenceBudgetValid risk)
    (ht : referenceBudgetTarget kind risk = some target) :
    (localObservationPrice input stage kind risk).toReal ≤
      (input.experiment stage).coefficient *
        (Real.log (1 / (target : ℝ)) + localPriceOffset input stage) := by
  have hp := referenceBudgetTarget_valid_floor kind risk target hv ht
  have hpR : 0 < (target : ℝ) := by exact_mod_cast hp.1
  have hpone : (target : ℝ) ≤ 1 := by
    exact_mod_cast hp.2.1.trans (by norm_num : (1 / 4 : ℚ) ≤ 1)
  have hlog : 0 ≤ Real.log (1 / (target : ℝ)) :=
    Real.log_nonneg ((le_div_iff₀ hpR).mpr (by simpa only [one_mul] using hpone))
  have hoff : 0 ≤ localPriceOffset input stage :=
    add_nonneg ((input.experiment stage).logIncrementBound_nonneg true) (by positivity)
  have hn := mul_nonneg (input.experiment stage).coefficient_pos.le (add_nonneg hlog hoff)
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (localObservationPrice_le_sharp input stage kind risk target hv ht)
  simpa only [ENNReal.toReal_ofReal hn] using h

theorem localPriceReal_finiteBad_eventual (input : StatisticalInput I) (stage : I.Stage)
    (j : ℕ+) (depth : ℕ) (hd : 1 ≤ depth) (horder : depth ≤ j.val + 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      (localObservationPrice input stage (.finiteBad j) risk).toReal ≤
        ((input.experiment stage).coefficient * (if depth = j.val + 1 then 1 else 0) + eta) *
          iteratedLog depth (1 / (risk : ℝ)) := by
  have hn := upper_of_ratio depth _ _ eta heta
    (controllerTarget_price_ratio j.val depth j.pos hd horder
      (input.experiment stage).coefficient (localPriceOffset input stage))
  filter_upwards [hn, self_mem_nhdsWithin, rationalRisk_eventually_le_quarter] with risk hr hp hq
  exact (localPriceReal_le_sharp input stage (.finiteBad j) risk _ ⟨hp, hq⟩ rfl).trans hr

theorem localPriceReal_noTool_eventual (input : StatisticalInput I) (stage : I.Stage)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      (localObservationPrice input stage .noTool risk).toReal ≤
        ((input.experiment stage).coefficient + eta) * iteratedLog 1 (1 / (risk : ℝ)) := by
  have hn := upper_of_ratio 1 _ _ eta heta
    (noTool_price_ratio (input.experiment stage).coefficient (localPriceOffset input stage))
  filter_upwards [hn, self_mem_nhdsWithin, rationalRisk_eventually_le_quarter] with risk hr hp hq
  exact (localPriceReal_le_sharp input stage .noTool risk _ ⟨hp, hq⟩ rfl).trans hr

theorem half_scale_bound (f : ℚ → ℝ) (coefficient : ℝ) (hc : 0 ≤ coefficient)
    (depth higher : ℕ) (hd : 1 ≤ depth) (horder : depth ≤ higher)
    (hf : ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      f risk ≤ coefficient * iteratedLog higher (1 / (risk : ℝ))) :
    ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      f (risk / 2) ≤ (2 * coefficient) * iteratedLog depth (1 / (risk : ℝ)) := by
  have hm : ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      iteratedLog higher (1 / ((risk / 2 : ℚ) : ℝ)) /
        iteratedLog depth (1 / (risk : ℝ)) < 2 := by
    by_cases he : higher = depth
    · subst higher
      exact (rationalRisk_iteratedLog_half_div_tendsto_one depth hd).eventually
        (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))
    · exact (rationalRisk_iteratedLog_half_div_tendsto_zero depth higher (by omega)).eventually
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 2))
  have hp := ((iteratedLog_tendsto_atTop depth).comp rationalInverse_tendsto_atTop).eventually_gt_atTop 0
  filter_upwards [rationalRisk_half_tendsto_zero.eventually hf, hm, hp] with risk hr hm hp
  have hb := ((div_lt_iff₀ hp).mp hm).le
  calc
    _ ≤ coefficient * iteratedLog higher (1 / ((risk / 2 : ℚ) : ℝ)) := hr
    _ ≤ coefficient * (2 * iteratedLog depth (1 / (risk : ℝ))) := mul_le_mul_of_nonneg_left hb hc
    _ = _ := by ring

theorem bad_scale_bound (f : ℚ → ℝ) (coefficient : ℝ) (hc : 0 ≤ coefficient)
    (j : ℕ+) (hf : ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      f risk ≤ coefficient * iteratedLog j.val (1 / (risk : ℝ))) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      (controllerTarget risk j.val : ℝ) * f (controllerBadRisk risk (controllerTarget risk j.val)) ≤ bound := by
  obtain ⟨bound, hb, hn⟩ := controllerTarget_scaledBadRisk_iteratedLog_bounded j.val j.pos 1 (by norm_num)
  simp only [one_mul] at hn
  refine ⟨coefficient * bound, mul_nonneg hc hb, ?_⟩
  filter_upwards [(controllerBadRisk_tendsto_zero j.val j.pos).eventually hf, hn] with risk hr hn
  have hq : 0 ≤ (controllerTarget risk j.val : ℝ) := by exact_mod_cast (controllerTarget_pos risk j.val).le
  calc
    _ ≤ (controllerTarget risk j.val : ℝ) *
        (coefficient * iteratedLog j.val (1 / (controllerBadRisk risk (controllerTarget risk j.val) : ℝ))) :=
      mul_le_mul_of_nonneg_left hr hq
    _ = coefficient * ((controllerTarget risk j.val : ℝ) *
        iteratedLog j.val (1 / (controllerBadRisk risk (controllerTarget risk j.val) : ℝ))) := by ring
    _ ≤ coefficient * bound := mul_le_mul_of_nonneg_left hn.2.2 hc

end PaperProofs.Retained.PRetObservationEnvelope119
