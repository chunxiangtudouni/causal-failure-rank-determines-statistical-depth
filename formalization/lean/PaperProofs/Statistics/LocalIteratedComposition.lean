module

public import PaperProofs.Statistics.LocalPrice
public import PaperProofs.Statistics.IteratedLogComparison
import Mathlib.Tactic.FieldSimp

/-!
Pure analytic composition for the original penalty induction. Positive
leading growth supplies divergence of the local penalty, including depth
zero. Positive log depths also make the outer minimum with the original
penalty eventually inactive. No new cost or policy object is introduced.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace PaperProofs.Statistics

theorem log_div_iteratedLog_succ_of_tendsto (t : ℝ → ℝ) (depth : ℕ) (B : ℝ)
    (hB : 0 < B)
    (ht : Tendsto (fun penalty => t penalty / iteratedLog depth penalty) atTop (𝓝 B)) :
    Tendsto (fun penalty => Real.log (t penalty) / iteratedLog (depth + 1) penalty)
      atTop (𝓝 1) := by
  have hs := iteratedLog_tendsto_atTop depth
  have hBs : Tendsto (fun penalty => B * iteratedLog depth penalty) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hB hs
  have hratio : Tendsto (fun penalty => t penalty / (B * iteratedLog depth penalty))
      atTop (𝓝 1) := by
    simpa only [div_div, mul_comm, div_self hB.ne'] using ht.div_const B
  have hnear : t ~[atTop] (fun penalty => B * iteratedLog depth penalty) :=
    (isEquivalent_iff_tendsto_one (hBs.eventually_ne_atTop 0)).mpr hratio
  have hlog := hnear.log hBs
  have hscale : (fun penalty => Real.log (B * iteratedLog depth penalty)) ~[atTop]
      (fun penalty => iteratedLog (depth + 1) penalty) := by
    simpa only [Function.comp_def, iteratedLog] using
      (iteratedLog_scale_isEquivalent 0 B hB).comp_tendsto hs
  exact (isEquivalent_iff_tendsto_one
    ((iteratedLog_tendsto_atTop (depth + 1)).eventually_ne_atTop 0)).mp (hlog.trans hscale)

namespace BinaryExperiment

theorem localValueReal_iteratedLog_succ_of_tendsto (E : BinaryExperiment)
    (t : ℝ → ℝ) (depth : ℕ) (B : ℝ) (hB : 0 < B)
    (ht : Tendsto (fun penalty => t penalty / iteratedLog depth penalty) atTop (𝓝 B)) :
    Tendsto (fun penalty => E.localValueReal (t penalty) /
      (E.coefficient * iteratedLog (depth + 1) penalty)) atTop (𝓝 1) := by
  have htTop : Tendsto t atTop atTop :=
    tendsto_atTop_of_ratio_pos hB ht (iteratedLog_tendsto_atTop depth)
  have hlocal := E.localLogarithmicPrice.comp htTop
  have hlog := log_div_iteratedLog_succ_of_tendsto t depth B hB ht
  have hprod : Tendsto (fun penalty =>
      (E.localValueReal (t penalty) / (E.coefficient * Real.log (t penalty))) *
        (Real.log (t penalty) / iteratedLog (depth + 1) penalty)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, one_mul] using hlocal.mul hlog
  apply hprod.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp htTop).eventually_ne_atTop 0,
    (iteratedLog_tendsto_atTop (depth + 1)).eventually_ne_atTop 0] with penalty hlogNe hnextNe
  change Real.log (t penalty) ≠ 0 at hlogNe
  field_simp [E.coefficient_pos.ne', hlogNe, hnextNe]

end BinaryExperiment

theorem div_id_tendsto_zero_of_iteratedLog_leading (f : ℝ → ℝ) (depth : ℕ)
    (hdepth : 1 ≤ depth) (C : ℝ)
    (hf : Tendsto (fun penalty => f penalty / iteratedLog depth penalty) atTop (𝓝 C)) :
    Tendsto (fun penalty => f penalty / penalty) atTop (𝓝 0) := by
  have hscale : Tendsto (fun penalty => iteratedLog depth penalty / penalty) atTop (𝓝 0) := by
    simpa only [iteratedLog] using iteratedLog_div_tendsto_zero_of_lt 0 depth hdepth
  have hprod : Tendsto (fun penalty => (f penalty / iteratedLog depth penalty) *
      (iteratedLog depth penalty / penalty)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hf.mul hscale
  apply hprod.congr'
  filter_upwards [(iteratedLog_tendsto_atTop depth).eventually_ne_atTop 0] with penalty hs
  field_simp [hs]

theorem min_id_eventually_eq_of_iteratedLog_leading (f : ℝ → ℝ) (depth : ℕ)
    (hdepth : 1 ≤ depth) (C : ℝ)
    (hf : Tendsto (fun penalty => f penalty / iteratedLog depth penalty) atTop (𝓝 C)) :
    (fun penalty => min penalty (f penalty)) =ᶠ[atTop] f := by
  have hzero := div_id_tendsto_zero_of_iteratedLog_leading f depth hdepth C hf
  filter_upwards [hzero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop (0 : ℝ)] with penalty hratio hpenalty
  exact min_eq_right ((div_lt_one hpenalty).mp hratio).le

theorem min_id_iteratedLog_tendsto_of_leading (f : ℝ → ℝ) (depth : ℕ)
    (hdepth : 1 ≤ depth) (C : ℝ)
    (hf : Tendsto (fun penalty => f penalty / iteratedLog depth penalty) atTop (𝓝 C)) :
    Tendsto (fun penalty => min penalty (f penalty) / iteratedLog depth penalty) atTop (𝓝 C) := by
  apply hf.congr'
  filter_upwards [min_id_eventually_eq_of_iteratedLog_leading f depth hdepth C hf] with penalty heq
  rw [heq]

end PaperProofs.Statistics
