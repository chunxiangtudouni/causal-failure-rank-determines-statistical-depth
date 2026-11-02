module

public import PaperProofs.Star.RootStarQuota_001
public import PaperProofs.Statistics.BadRiskAsymptotics

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace RootStarEnvelope

open PaperProofs.Star PaperProofs.Star.Parameters PaperProofs.Statistics

noncomputable def badBudget (r : ℝ) (j : ℕ) : ℝ := min (1 / 4) (r / starTargetReal r j)

theorem inverse_tendsto : Tendsto (fun r : ℝ => 1 / r) (𝓝[>] 0) atTop := by
  simpa only [one_div] using (tendsto_inv_nhdsGT_zero : Tendsto (fun r : ℝ => r⁻¹) (𝓝[>] 0) atTop)

theorem eventually_quarter : ∀ᶠ r : ℝ in 𝓝[>] 0, r ≤ 1 / 4 :=
  ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds).mono
    (fun _ h => h.le)

theorem bad_positive (r : ℝ) (hr : 0 < r) (j : ℕ) : 0 < badBudget r j :=
  lt_min (by norm_num) (div_pos hr (RootStarQuota.starTarget_pos r j))

theorem bad_bounds (r : ℝ) (hr : 0 < r) (hq : r ≤ 1 / 4) (j : ℕ) :
    r ≤ badBudget r j ∧ badBudget r j ≤ 1 / 4 := by
  have ht := RootStarQuota.starTarget_pos r j
  have hquarter := RootStarQuota.starTarget_le_quarter r j
  refine ⟨le_min hq ?_, min_le_left _ _⟩
  apply (le_div_iff₀ ht).mpr
  nlinarith only [hr, hquarter]

theorem target_product_le (r : ℝ) (j : ℕ) :
    starTargetReal r j * badBudget r j ≤ r := by
  have ht := RootStarQuota.starTarget_pos r j
  calc
    _ ≤ starTargetReal r j * (r / starTargetReal r j) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) ht.le
    _ = r := by field_simp [ht.ne']

theorem target_log_difference (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun r : ℝ => Real.log (1 / starTargetReal r j) - iteratedLog (j + 1) (1 / r))
      (𝓝[>] 0) (𝓝 (Real.log 4 + Real.log (1 / Real.log 2))) := by
  simpa only [Function.comp_def, starTargetReal, one_div_one_div] using
    (analyticControllerTarget_log_difference j hj).comp inverse_tendsto

theorem target_mul_iteratedLog (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun r : ℝ => starTargetReal r j * iteratedLog j (1 / r))
      (𝓝[>] 0) (𝓝 (Real.log 2 / 4)) := by
  simpa only [Function.comp_def, starTargetReal] using
    (analyticControllerTarget_mul_iteratedLog j hj).comp inverse_tendsto

theorem initial_growth :
    Tendsto (fun r : ℝ => r * (1 + (analyticControllerB (1 / r) 1 : ℝ))) (𝓝[>] 0) (𝓝 0) := by
  have hratio := (analyticControllerB_add_one_ratio 1 (by omega)).comp inverse_tendsto
  have hlog : Tendsto (fun r : ℝ => Real.log (1 / r) / (1 / r)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, one_mul, add_zero, pow_one] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp inverse_tendsto
  have hp := hratio.mul hlog
  apply (show Tendsto (fun r : ℝ =>
      ((1 + (analyticControllerB (1 / r) 1 : ℝ)) / iteratedLog 1 (1 / r)) *
        (Real.log (1 / r) / (1 / r))) (𝓝[>] 0) (𝓝 0) from
      by simpa only [Function.comp_def, mul_zero] using hp).congr'
  filter_upwards [self_mem_nhdsWithin,
    (Real.tendsto_log_atTop.comp inverse_tendsto).eventually_ne_atTop 0] with r hr hlogzero
  change Real.log (1 / r) ≠ 0 at hlogzero
  have hrpos : 0 < r := hr
  simp only [iteratedLog]
  field_simp [hlogzero, hrpos.ne']

theorem bad_tendsto_zero (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun r : ℝ => badBudget r j) (𝓝[>] 0) (𝓝 0) := by
  have hu : Tendsto (fun r : ℝ => 4 * r * (1 + (analyticControllerB (1 / r) 1 : ℝ)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, mul_assoc] using initial_growth.const_mul 4
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (bad_positive r hr j).le
  · filter_upwards [self_mem_nhdsWithin, eventually_quarter] with r hr hq
    have hrpos : 0 < r := hr
    have hi := RootStarQuota.analytic_initial_bounds r hr hq
    have hb : analyticControllerB (1 / r) j ≤ analyticControllerB (1 / r) 1 :=
      (thresholdSequence_bounds (analyticControllerB (1 / r) 1) hi.1 j hj).2
    have hbR : (analyticControllerB (1 / r) j : ℝ) ≤ (analyticControllerB (1 / r) 1 : ℝ) := by exact_mod_cast hb
    calc
      _ ≤ r / starTargetReal r j := min_le_right _ _
      _ = 4 * r * (1 + (analyticControllerB (1 / r) j : ℝ)) := by
        rw [starTargetReal]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hbR])
        (mul_nonneg (by norm_num) hrpos.le)

theorem bad_tendsto_positive (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun r : ℝ => badBudget r j) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨bad_tendsto_zero j hj, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact bad_positive r hr j

theorem weighted_bad_iteratedLog_bounded (j : ℕ) (hj : 1 ≤ j) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      0 ≤ iteratedLog j (1 / badBudget r j) ∧
      0 ≤ starTargetReal r j * iteratedLog j (1 / badBudget r j) ∧
      starTargetReal r j * iteratedLog j (1 / badBudget r j) ≤ bound := by
  obtain ⟨threshold, _ht, hmono⟩ := iteratedLog_positive_mono_tail j
  have hinv := inverse_tendsto.comp (bad_tendsto_positive j hj)
  have hlarge := hinv.eventually_ge_atTop threshold
  have hproduct := (target_mul_iteratedLog j hj).eventually
    (eventually_lt_nhds (by linarith : Real.log 2 / 4 < Real.log 2 / 4 + 1))
  refine ⟨Real.log 2 / 4 + 1, by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); linarith, ?_⟩
  filter_upwards [self_mem_nhdsWithin, eventually_quarter, hlarge, hproduct] with r hr hq hl hp
  have hb := bad_bounds r hr hq j
  have hi : 1 / badBudget r j ≤ 1 / r := one_div_le_one_div_of_le hr hb.1
  have hm := hmono _ _ hl hi
  have ht := (RootStarQuota.starTarget_pos r j).le
  exact ⟨hm.1.le, mul_nonneg ht hm.1.le, (mul_le_mul_of_nonneg_left hm.2 ht).trans hp.le⟩

theorem bounded_of_tendsto {f : ℝ → ℝ} {c : ℝ} (h : Tendsto f (𝓝[>] 0) (𝓝 c)) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, |f r| ≤ bound := by
  refine ⟨|c| + 1, by positivity, ?_⟩
  exact (h.abs.eventually (eventually_lt_nhds (by linarith : |c| < |c| + 1))).mono (fun _ hr => hr.le)

theorem positive_cutoff {predicate : ℝ → Prop} (h : ∀ᶠ r : ℝ in 𝓝[>] 0, predicate r) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ r : ℝ, 0 < r → r < cutoff → predicate r := by
  obtain ⟨neighborhood, hneighborhood, hsubset⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h
  obtain ⟨cutoff, hcutoff, hball⟩ := Metric.mem_nhds_iff.mp hneighborhood
  refine ⟨cutoff, hcutoff, ?_⟩
  intro r hr hs
  apply hsubset
  refine ⟨hball ?_, hr⟩
  change dist r (0 : ℝ) < cutoff
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hr] using hs

end RootStarEnvelope
