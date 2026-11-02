module

public import PaperProofs.Statistics.LocalPrice
public import PaperProofs.Statistics.IteratedLog
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
The cancellation estimate in price-proofs.tex:128--140. No lower bound on
the difference of two continuation values is needed. The only asymptotic
input is a positive finite leading term for the bad continuation itself.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace PaperProofs.Statistics

theorem log_one_add_div_tendsto_zero :
    Tendsto (fun t : ℝ => Real.log (1 + t) / t) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1 + t) atTop atTop :=
    tendsto_const_nhds.add_atTop tendsto_id
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp ht
  have hden (t : ℝ) : 1 * (1 + t) + (-1) = t := by ring
  simpa only [Function.comp_def, pow_one, hden] using h

namespace BinaryExperiment

theorem localValueReal_sublinear (E : BinaryExperiment) :
    Tendsto (fun t : ℝ => E.localValueReal t / t) atTop (𝓝 0) := by
  obtain ⟨K, _, hK⟩ := E.globalLogarithmicEnvelope
  have hupper : Tendsto (fun t : ℝ => K * Real.log (1 + t) / t) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using
      (tendsto_const_nhds.mul log_one_add_div_tendsto_zero :
        Tendsto (fun t : ℝ => K * (Real.log (1 + t) / t)) atTop (𝓝 (K * 0)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ : ℝ => (0 : ℝ)) (h := fun t => K * Real.log (1 + t) / t)
    tendsto_const_nhds hupper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact div_nonneg (E.localValueReal_nonneg t) ht.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (div_le_div_iff_of_pos_right ht).mpr (hK t ht.le)

/-- This estimate allows the good and bad leading terms to cancel exactly.
There is no assumption that their difference tends to infinity or is a
positive fraction of the bad continuation. -/
theorem localValue_difference_negligible (E : BinaryExperiment)
    (good bad scale : ℝ → ℝ) (B : ℝ) (hB : 0 < B)
    (hscale : Tendsto scale atTop atTop)
    (hbad : Tendsto (fun t => bad t / scale t) atTop (𝓝 B))
    (horder : ∀ᶠ t in atTop, 0 ≤ good t ∧ good t ≤ bad t) :
    Tendsto (fun t => E.localValueReal (bad t - good t) / scale t) atTop (𝓝 0) := by
  have hscaleNe : ∀ᶠ t in atTop, scale t ≠ 0 := hscale.eventually_ne_atTop 0
  have hbadTop : Tendsto bad atTop atTop := by
    have hprod := Filter.Tendsto.pos_mul_atTop hB hbad hscale
    apply hprod.congr'
    filter_upwards [hscaleNe] with t ht
    exact div_mul_cancel₀ (bad t) ht
  have hbadPos : ∀ᶠ t in atTop, 0 < bad t := hbadTop.eventually_gt_atTop 0
  obtain ⟨K, hK, hbound⟩ := E.globalLogarithmicEnvelope
  have hupper : Tendsto (fun t => K * Real.log (1 + bad t) / bad t) atTop (𝓝 0) := by
    have hlog := log_one_add_div_tendsto_zero.comp hbadTop
    simpa only [mul_div_assoc, mul_zero] using
      (tendsto_const_nhds.mul hlog :
        Tendsto (fun t => K * (Real.log (1 + bad t) / bad t)) atTop (𝓝 (K * 0)))
  have hratio : Tendsto (fun t => E.localValueReal (bad t - good t) / bad t) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun _ : ℝ => (0 : ℝ)) (h := fun t => K * Real.log (1 + bad t) / bad t)
      tendsto_const_nhds hupper
    · filter_upwards [hbadPos] with t ht
      exact div_nonneg (E.localValueReal_nonneg _) ht.le
    · filter_upwards [hbadPos, horder] with t ht ho
      apply (div_le_div_iff_of_pos_right ht).mpr
      apply (hbound _ (sub_nonneg.mpr ho.2)).trans
      apply mul_le_mul_of_nonneg_left _ hK
      exact Real.log_le_log (by linarith : 0 < 1 + (bad t - good t)) (by linarith)
  have hprod : Tendsto (fun t =>
      (E.localValueReal (bad t - good t) / bad t) * (bad t / scale t)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hratio.mul hbad
  apply hprod.congr'
  filter_upwards [hscaleNe, hbadPos] with t hs hb
  field_simp [hs, ne_of_gt hb]

theorem localValue_iteratedLog_difference_negligible (E : BinaryExperiment)
    (good bad : ℝ → ℝ) (depth : ℕ) (B : ℝ) (hB : 0 < B)
    (hbad : Tendsto (fun t => bad t / iteratedLog depth t) atTop (𝓝 B))
    (horder : ∀ᶠ t in atTop, 0 ≤ good t ∧ good t ≤ bad t) :
    Tendsto (fun t => E.localValueReal (bad t - good t) / iteratedLog depth t)
      atTop (𝓝 0) :=
  E.localValue_difference_negligible good bad (iteratedLog depth) B hB
    (iteratedLog_tendsto_atTop depth) hbad horder

end BinaryExperiment
end PaperProofs.Statistics
