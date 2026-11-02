module

public import PaperProofs.Statistics.ControllerThresholds

/-!
Pure numerical B18 lemmas for the ORIGINAL controllerBadRisk and targets.
These are proofs, not additional bad-child performance hypotheses.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace PaperProofs.Statistics

theorem rationalRisk_cast_tendsto_zero :
    Tendsto (fun risk : ℚ => (risk : ℝ)) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  simpa only [Rat.cast_zero] using
    (Rat.continuous_coe_real.tendsto 0).mono_left nhdsWithin_le_nhds

theorem rationalRisk_eventually_le_quarter :
    ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0), risk ≤ 1 / 4 := by
  have h : ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0), risk < 1 / 4 :=
    (eventually_lt_nhds (by norm_num : (0 : ℚ) < 1 / 4)).filter_mono nhdsWithin_le_nhds
  exact h.mono (fun _ hr => hr.le)

/-- The first original integer threshold grows only logarithmically. -/
theorem risk_mul_controllerB_one_tendsto_zero :
    Tendsto (fun risk : ℚ => (risk : ℝ) * (1 + (controllerB risk 1 : ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have hratio := (analyticControllerB_add_one_ratio 1 (by omega)).comp rationalInverse_tendsto_atTop
  have hlog : Tendsto (fun risk : ℚ => Real.log (1 / (risk : ℝ)) / (1 / (risk : ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    simpa only [Function.comp_def, one_mul, add_zero, pow_one] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp rationalInverse_tendsto_atTop
  have hp := hratio.mul hlog
  apply (show Tendsto (fun risk : ℚ =>
      ((1 + (analyticControllerB (1 / (risk : ℝ)) 1 : ℝ)) / iteratedLog 1 (1 / (risk : ℝ))) *
        (Real.log (1 / (risk : ℝ)) / (1 / (risk : ℝ))))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) from by simpa only [Function.comp_def, mul_zero] using hp).congr'
  filter_upwards [self_mem_nhdsWithin,
    (Real.tendsto_log_atTop.comp rationalInverse_tendsto_atTop).eventually_ne_atTop 0]
    with risk hrisk hlogzero
  have hr : (0 : ℚ) < risk := hrisk
  have hrR : (0 : ℝ) < (risk : ℝ) := by exact_mod_cast hr
  change Real.log (1 / (risk : ℝ)) ≠ 0 at hlogzero
  rw [controllerB_eq_analytic risk hr 1]
  simp only [iteratedLog]
  field_simp [hlogzero, hrR.ne']

/-- No risk update is replaced by an asymptotic surrogate. -/
theorem controllerBadRisk_le_firstThreshold (risk : ℚ) (j : ℕ)
    (hrisk : 0 < risk) (hquarter : risk ≤ 1 / 4) (hj : 1 ≤ j) :
    (controllerBadRisk risk (controllerTarget risk j) : ℝ) ≤
      2 * (risk : ℝ) * (1 + (controllerB risk 1 : ℝ)) := by
  have hB : (controllerB risk j : ℝ) ≤ (controllerB risk 1 : ℝ) := by
    exact_mod_cast (controllerB_bounds risk hrisk hquarter j hj).2.1
  have hraw : controllerBadRisk risk (controllerTarget risk j) ≤ risk / (2 * controllerTarget risk j) :=
    min_le_right _ _
  have hrawR : (controllerBadRisk risk (controllerTarget risk j) : ℝ) ≤
      (risk : ℝ) / (2 * (controllerTarget risk j : ℝ)) := by exact_mod_cast hraw
  have hrR : (0 : ℝ) < (risk : ℝ) := by exact_mod_cast hrisk
  calc
    _ ≤ (risk : ℝ) / (2 * (controllerTarget risk j : ℝ)) := hrawR
    _ = 2 * (risk : ℝ) * (1 + (controllerB risk j : ℝ)) := by
      rw [controllerTarget_real]
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith : 1 + (controllerB risk j : ℝ) ≤ 1 + (controllerB risk 1 : ℝ)) (by positivity)

theorem controllerBadRisk_real_tendsto_zero (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun risk : ℚ => (controllerBadRisk risk (controllerTarget risk j) : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have hupper : Tendsto (fun risk : ℚ => 2 * (risk : ℝ) * (1 + (controllerB risk 1 : ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    simpa only [mul_zero, mul_assoc] using risk_mul_controllerB_one_tendsto_zero.const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [self_mem_nhdsWithin, rationalRisk_eventually_le_quarter] with risk hr hq
    exact_mod_cast (controllerBadRisk_positive risk (controllerTarget risk j) hr hq
      (controllerTarget_pos risk j) (controllerTarget_le_quarter risk j)).le
  · filter_upwards [self_mem_nhdsWithin, rationalRisk_eventually_le_quarter] with risk hr hq
    exact controllerBadRisk_le_firstThreshold risk j hr hq hj

/-- The exact rational r' tends to zero INSIDE the positive rational domain,
so a previously proved suffix asymptotic can be composed directly. -/
theorem controllerBadRisk_tendsto_zero (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun risk : ℚ => controllerBadRisk risk (controllerTarget risk j))
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · apply Rat.isEmbedding_coe_real.tendsto_nhds_iff.mpr
    simpa only [Function.comp_def, Rat.cast_zero] using controllerBadRisk_real_tendsto_zero j hj
  · filter_upwards [self_mem_nhdsWithin, rationalRisk_eventually_le_quarter] with risk hr hq
    exact controllerBadRisk_positive risk (controllerTarget risk j) hr hq
      (controllerTarget_pos risk j) (controllerTarget_le_quarter risk j)

theorem scaled_controllerBadRisk_tendsto_zero (j : ℕ) (hj : 1 ≤ j)
    (scale : ℚ) (hscale : 0 < scale) :
    Tendsto (fun risk : ℚ => scale * controllerBadRisk risk (controllerTarget risk j))
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
  have hbad := controllerBadRisk_tendsto_zero j hj
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [mul_zero] using
      ((tendsto_nhdsWithin_iff.mp hbad).1.const_mul scale)
  · filter_upwards [self_mem_nhdsWithin, rationalRisk_eventually_le_quarter] with risk hr hq
    exact mul_pos hscale (controllerBadRisk_positive risk (controllerTarget risk j) hr hq
      (controllerTarget_pos risk j) (controllerTarget_le_quarter risk j))

/-- Real log is not globally monotone on its totalized domain. This lemma
provides the genuine positive tail on which each fixed iterlog is monotone. -/
theorem iteratedLog_positive_mono_tail (depth : ℕ) :
    ∃ threshold : ℝ, 0 < threshold ∧ ∀ (x y : ℝ), threshold ≤ x → x ≤ y →
      0 < iteratedLog depth x ∧ iteratedLog depth x ≤ iteratedLog depth y := by
  induction depth with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro x y hx hxy
    exact ⟨by simpa only [iteratedLog] using (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx), hxy⟩
  | succ depth ih =>
    obtain ⟨old, _hold, hmono⟩ := ih
    obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.mp ((iteratedLog_tendsto_atTop depth).eventually_ge_atTop 2)
    refine ⟨max 1 (max old cutoff), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
    intro x y hx hxy
    have hox : old ≤ x := (le_max_left old cutoff).trans ((le_max_right 1 _).trans hx)
    have hcx : cutoff ≤ x := (le_max_right old cutoff).trans ((le_max_right 1 _).trans hx)
    have htwo := hcutoff x hcx
    have hm := hmono x y hox hxy
    change 0 < Real.log (iteratedLog depth x) ∧ Real.log (iteratedLog depth x) ≤ Real.log (iteratedLog depth y)
    exact ⟨Real.log_pos (by linarith), Real.log_le_log hm.1 hm.2⟩

theorem iteratedLog_eventually_one_le (depth : ℕ) :
    ∀ᶠ z : ℝ in atTop, 1 ≤ iteratedLog depth z :=
  (iteratedLog_tendsto_atTop depth).eventually_ge_atTop 1

/-- Uniform finite bound for the EXACT original bad-child scale. Scale=1
is paper r', while scale=2 is the actual fresh child parser budget. -/
theorem controllerTarget_scaledBadRisk_iteratedLog_bounded (j : ℕ) (hj : 1 ≤ j)
    (scale : ℚ) (hscale : 1 ≤ scale) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      0 ≤ iteratedLog j (1 / ((scale * controllerBadRisk risk (controllerTarget risk j) : ℚ) : ℝ)) ∧
      0 ≤ (controllerTarget risk j : ℝ) *
        iteratedLog j (1 / ((scale * controllerBadRisk risk (controllerTarget risk j) : ℚ) : ℝ)) ∧
      (controllerTarget risk j : ℝ) *
        iteratedLog j (1 / ((scale * controllerBadRisk risk (controllerTarget risk j) : ℚ) : ℝ)) ≤ bound := by
  obtain ⟨threshold, _hthreshold, hmono⟩ := iteratedLog_positive_mono_tail j
  have hs : (0 : ℚ) < scale := lt_of_lt_of_le (by norm_num) hscale
  have hinv := rationalInverse_tendsto_atTop.comp (scaled_controllerBadRisk_tendsto_zero j hj scale hs)
  have hlarge := hinv.eventually_ge_atTop threshold
  have hproduct := (controllerTarget_mul_iteratedLog_tendsto j hj).eventually
    (eventually_lt_nhds (by linarith : Real.log 2 / 4 < Real.log 2 / 4 + 1))
  refine ⟨Real.log 2 / 4 + 1, by have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num); linarith, ?_⟩
  filter_upwards [self_mem_nhdsWithin, rationalRisk_eventually_le_quarter, hlarge, hproduct]
    with risk hr hq hlarge hproduct
  have hbad := controllerBadRisk_bounds risk (controllerTarget risk j) hr hq
    (controllerTarget_pos risk j) (controllerTarget_le_quarter risk j)
  have hbadPos := controllerBadRisk_positive risk (controllerTarget risk j) hr hq
    (controllerTarget_pos risk j) (controllerTarget_le_quarter risk j)
  have hrR : (0 : ℝ) < (risk : ℝ) := by exact_mod_cast (show (0 : ℚ) < risk from hr)
  have horderQ : risk ≤ scale * controllerBadRisk risk (controllerTarget risk j) :=
    hbad.1.trans (le_mul_of_one_le_left hbadPos.le hscale)
  have horderR : (risk : ℝ) ≤ ((scale * controllerBadRisk risk (controllerTarget risk j) : ℚ) : ℝ) := by
    exact_mod_cast horderQ
  have hinverse : 1 / ((scale * controllerBadRisk risk (controllerTarget risk j) : ℚ) : ℝ) ≤
      1 / (risk : ℝ) := one_div_le_one_div_of_le hrR horderR
  have hm := hmono _ _ hlarge hinverse
  have hp : (0 : ℝ) ≤ (controllerTarget risk j : ℝ) := by exact_mod_cast (controllerTarget_pos risk j).le
  exact ⟨hm.1.le, mul_nonneg hp hm.1.le,
    (mul_le_mul_of_nonneg_left hm.2 hp).trans hproduct.le⟩

/-- Converts the rational positive-side filter statement to the original
paper's positive REAL cutoff, without choosing a rationalization function. -/
theorem rationalEventually_positive_cutoff {P : ℚ → Prop}
    (hP : ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0), P risk) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ risk : ℚ, 0 < risk → (risk : ℝ) < cutoff → P risk := by
  obtain ⟨neighborhood, hneighborhood, hsubset⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hP
  obtain ⟨cutoff, hcutoff, hball⟩ := Metric.mem_nhds_iff.mp hneighborhood
  refine ⟨cutoff, hcutoff, ?_⟩
  intro risk hrisk hsmall
  apply hsubset
  refine ⟨hball ?_, hrisk⟩
  change dist risk (0 : ℚ) < cutoff
  rw [Rat.dist_eq, Rat.cast_zero, sub_zero, abs_of_pos (by exact_mod_cast hrisk)]
  exact hsmall

theorem controllerTarget_scaledBadRisk_iteratedLog_cutoff (j : ℕ) (hj : 1 ≤ j)
    (scale : ℚ) (hscale : 1 ≤ scale) :
    ∃ bound cutoff : ℝ, 0 ≤ bound ∧ 0 < cutoff ∧
      ∀ risk : ℚ, 0 < risk → (risk : ℝ) < cutoff →
        0 ≤ iteratedLog j (1 / ((scale * controllerBadRisk risk (controllerTarget risk j) : ℚ) : ℝ)) ∧
        0 ≤ (controllerTarget risk j : ℝ) *
          iteratedLog j (1 / ((scale * controllerBadRisk risk (controllerTarget risk j) : ℚ) : ℝ)) ∧
        (controllerTarget risk j : ℝ) *
          iteratedLog j (1 / ((scale * controllerBadRisk risk (controllerTarget risk j) : ℚ) : ℝ)) ≤ bound := by
  obtain ⟨bound, hbound, heventual⟩ := controllerTarget_scaledBadRisk_iteratedLog_bounded j hj scale hscale
  obtain ⟨cutoff, hcutoff, hresult⟩ := rationalEventually_positive_cutoff heventual
  exact ⟨bound, cutoff, hbound, hcutoff, hresult⟩

end PaperProofs.Statistics
