module

public import PaperProofs.Statistics.BadRiskAsymptotics

/-!
Pure analytic comparisons used by the ORIGINAL B18 suffix induction.
Distinct fixed log depths and constant rescalings are compared on their
positive tail; no policy costs or continuation guarantees are assumed.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace PaperProofs.Statistics

theorem iteratedLog_succ_div_tendsto_zero (depth : ℕ) :
    Tendsto (fun z : ℝ => iteratedLog (depth + 1) z / iteratedLog depth z)
      atTop (𝓝 0) := by
  simpa only [Function.comp_def, pow_one, one_mul, add_zero, iteratedLog] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (iteratedLog_tendsto_atTop depth)

theorem iteratedLog_add_succ_div_tendsto_zero (depth extra : ℕ) :
    Tendsto (fun z : ℝ => iteratedLog (depth + extra + 1) z / iteratedLog depth z)
      atTop (𝓝 0) := by
  induction extra with
  | zero => simpa only [Nat.add_zero] using iteratedLog_succ_div_tendsto_zero depth
  | succ extra ih =>
    have hp := (iteratedLog_succ_div_tendsto_zero (depth + extra + 1)).mul ih
    apply (show Tendsto (fun z : ℝ =>
        (iteratedLog (depth + extra + 1 + 1) z / iteratedLog (depth + extra + 1) z) *
          (iteratedLog (depth + extra + 1) z / iteratedLog depth z)) atTop (𝓝 0)
        from by simpa only [zero_mul] using hp).congr'
    filter_upwards [(iteratedLog_tendsto_atTop (depth + extra + 1)).eventually_ne_atTop 0,
      (iteratedLog_tendsto_atTop depth).eventually_ne_atTop 0] with z hz hd
    have hn : depth + (extra + 1) + 1 = depth + extra + 1 + 1 := by omega
    rw [hn]
    field_simp [hz, hd]

theorem iteratedLog_div_tendsto_zero_of_lt (lower upper : ℕ) (hlt : lower < upper) :
    Tendsto (fun z : ℝ => iteratedLog upper z / iteratedLog lower z)
      atTop (𝓝 0) := by
  obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.mpr hlt)
  have hu : upper = lower + extra + 1 := by omega
  rw [hu]
  exact iteratedLog_add_succ_div_tendsto_zero lower extra

theorem iteratedLog_scale_isEquivalent (depth : ℕ) (scale : ℝ) (hscale : 0 < scale) :
    (fun z : ℝ => iteratedLog (depth + 1) (scale * z)) ~[atTop]
      (fun z => iteratedLog (depth + 1) z) := by
  induction depth with
  | zero =>
    have hlog := Real.tendsto_log_atTop
    have hden := hlog.eventually_ne_atTop 0
    apply (isEquivalent_iff_tendsto_one hden).mpr
    have hp : Tendsto (fun z : ℝ => Real.log scale / Real.log z + 1) atTop (𝓝 1) := by
      simpa only [zero_add] using
        (tendsto_const_nhds.div_atTop hlog : Tendsto (fun z : ℝ => Real.log scale / Real.log z) atTop (𝓝 0)).add_const 1
    apply hp.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ), hden] with z hz hd
    change Real.log scale / Real.log z + 1 = Real.log (scale * z) / Real.log z
    rw [Real.log_mul hscale.ne' hz.ne', add_div, div_self hd]
  | succ depth ih =>
    exact ih.log (iteratedLog_tendsto_atTop (depth + 1))

theorem iteratedLog_scale_div_tendsto_one (depth : ℕ) (hdepth : 1 ≤ depth)
    (scale : ℝ) (hscale : 0 < scale) :
    Tendsto (fun z : ℝ => iteratedLog depth (scale * z) / iteratedLog depth z)
      atTop (𝓝 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show depth ≠ 0 by omega)
  exact (isEquivalent_iff_tendsto_one ((iteratedLog_tendsto_atTop (n + 1)).eventually_ne_atTop 0)).mp
    (iteratedLog_scale_isEquivalent n scale hscale)

theorem iteratedLog_scaled_div_tendsto_zero_of_lt (lower upper : ℕ) (hlt : lower < upper)
    (scale : ℝ) (hscale : 0 < scale) :
    Tendsto (fun z : ℝ => iteratedLog upper (scale * z) / iteratedLog lower z)
      atTop (𝓝 0) := by
  have hp := (iteratedLog_scale_div_tendsto_one upper (by omega) scale hscale).mul
    (iteratedLog_div_tendsto_zero_of_lt lower upper hlt)
  apply (show Tendsto (fun z : ℝ =>
      (iteratedLog upper (scale * z) / iteratedLog upper z) *
        (iteratedLog upper z / iteratedLog lower z)) atTop (𝓝 0)
      from by simpa only [one_mul] using hp).congr'
  filter_upwards [(iteratedLog_tendsto_atTop upper).eventually_ne_atTop 0,
    (iteratedLog_tendsto_atTop lower).eventually_ne_atTop 0] with z hu hl
  field_simp [hu, hl]

theorem rationalRisk_iteratedLog_half_div_tendsto_one (depth : ℕ) (hdepth : 1 ≤ depth) :
    Tendsto (fun risk : ℚ => iteratedLog depth (1 / ((risk / 2 : ℚ) : ℝ)) /
      iteratedLog depth (1 / (risk : ℝ))) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
  have h := (iteratedLog_scale_div_tendsto_one depth hdepth 2 (by norm_num)).comp
    rationalInverse_tendsto_atTop
  apply h.congr'
  exact Filter.Eventually.of_forall (fun risk => by
    simp only [Function.comp_def, Rat.cast_div, Rat.cast_ofNat]
    congr 2
    ring)

theorem rationalRisk_iteratedLog_half_div_tendsto_zero (lower upper : ℕ) (hlt : lower < upper) :
    Tendsto (fun risk : ℚ => iteratedLog upper (1 / ((risk / 2 : ℚ) : ℝ)) /
      iteratedLog lower (1 / (risk : ℝ))) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have h := (iteratedLog_scaled_div_tendsto_zero_of_lt lower upper hlt 2 (by norm_num)).comp
    rationalInverse_tendsto_atTop
  apply h.congr'
  exact Filter.Eventually.of_forall (fun risk => by
    simp only [Function.comp_def, Rat.cast_div, Rat.cast_ofNat]
    congr 2
    ring)

theorem rationalRisk_half_tendsto_zero :
    Tendsto (fun risk : ℚ => risk / 2) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [zero_div, id_eq] using
      ((tendsto_id.div_const (2 : ℚ)).mono_left nhdsWithin_le_nhds :
        Tendsto (fun risk : ℚ => risk / 2) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 ((0 : ℚ) / 2)))
  · filter_upwards [self_mem_nhdsWithin] with risk hrisk
    change 0 < risk / 2
    exact div_pos (show (0 : ℚ) < risk from hrisk) (by norm_num)

/-- The actual finite-bad test starts with local risk budget/2. Its leading
log has depth j+1, so it contributes exactly when the parent rank is j+1. -/
theorem controllerTarget_half_log_div_iteratedLog (j depth : ℕ) (hj : 1 ≤ j)
    (hdepth : 1 ≤ depth) (horder : depth ≤ j + 1) :
    Tendsto (fun risk : ℚ => Real.log (1 / (controllerTarget (risk / 2) j : ℝ)) /
      iteratedLog depth (1 / (risk : ℝ))) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (if depth = j + 1 then 1 else 0)) := by
  have hdiff := (controllerTarget_log_difference_tendsto j hj).comp rationalRisk_half_tendsto_zero
  have hden := (iteratedLog_tendsto_atTop depth).comp rationalInverse_tendsto_atTop
  have hnegligible := hdiff.div_atTop hden
  have hmain : Tendsto (fun risk : ℚ => iteratedLog (j + 1) (1 / ((risk / 2 : ℚ) : ℝ)) /
      iteratedLog depth (1 / (risk : ℝ))) (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (if depth = j + 1 then 1 else 0)) := by
    by_cases heq : depth = j + 1
    · subst depth
      simpa only [ite_true] using rationalRisk_iteratedLog_half_div_tendsto_one (j + 1) (by omega)
    · simpa only [heq, ite_false] using
        rationalRisk_iteratedLog_half_div_tendsto_zero depth (j + 1) (by omega)
  apply (show Tendsto (fun risk : ℚ =>
      (Real.log (1 / (controllerTarget (risk / 2) j : ℝ)) -
        iteratedLog (j + 1) (1 / ((risk / 2 : ℚ) : ℝ))) / iteratedLog depth (1 / (risk : ℝ)) +
          iteratedLog (j + 1) (1 / ((risk / 2 : ℚ) : ℝ)) / iteratedLog depth (1 / (risk : ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (if depth = j + 1 then 1 else 0))
      from by simpa only [Function.comp_def, zero_add] using hnegligible.add hmain).congr'
  exact Filter.Eventually.of_forall (fun risk => by ring)

theorem controllerTarget_half_price_div_iteratedLog (j depth : ℕ) (hj : 1 ≤ j)
    (hdepth : 1 ≤ depth) (horder : depth ≤ j + 1) (coefficient offset : ℝ) :
    Tendsto (fun risk : ℚ => coefficient *
      (Real.log (1 / (controllerTarget (risk / 2) j : ℝ)) + offset) /
        iteratedLog depth (1 / (risk : ℝ))) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (coefficient * (if depth = j + 1 then 1 else 0))) := by
  have hlog := controllerTarget_half_log_div_iteratedLog j depth hj hdepth horder
  have hz : Tendsto (fun risk : ℚ => offset / iteratedLog depth (1 / (risk : ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((iteratedLog_tendsto_atTop depth).comp rationalInverse_tendsto_atTop)
  apply (show Tendsto (fun risk : ℚ => coefficient *
      (Real.log (1 / (controllerTarget (risk / 2) j : ℝ)) / iteratedLog depth (1 / (risk : ℝ)) +
        offset / iteratedLog depth (1 / (risk : ℝ))))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (coefficient * (if depth = j + 1 then 1 else 0)))
      from by simpa only [add_zero] using (hlog.add hz).const_mul coefficient).congr'
  exact Filter.Eventually.of_forall (fun risk => by ring)

end PaperProofs.Statistics
