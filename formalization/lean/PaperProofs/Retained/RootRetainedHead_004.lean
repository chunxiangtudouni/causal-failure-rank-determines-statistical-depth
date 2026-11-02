module

public import PaperProofs.Retained.RootRetainedHead_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open Filter Asymptotics
open scoped Topology ENNReal

namespace RootRetainedHead

open PaperProofs.Common PaperProofs.Retained PaperProofs.Statistics

variable {I : Instance}

theorem nativeLowerPriceLaw_of_recursion (input : StatisticalInput I) (hrec : FreshPenaltyRecursion input) :
    NativeLowerPriceLaw input := by
  intro depth hg ε hε
  have hfinite : girth I ≠ ⊤ := by rw [hg]; exact ENat.natCast_ne_top depth
  have hC := headCoefficient_pos input hfinite
  have hn : 0 < I.stageCount := by
    obtain ⟨i, _⟩ := girthHeads_nonempty I hfinite
    have hi : i.val < I.stageCount := i.isLt
    omega
  have hlim := head_leading input hrec depth hg
  let scale : ℝ → ℝ := fun penalty => headCoefficient input * iteratedLog depth penalty
  have hscale : Tendsto scale atTop atTop :=
    Filter.Tendsto.const_mul_atTop hC (iteratedLog_tendsto_atTop depth)
  have hratio : ∀ᶠ penalty in atTop,
      1 - ε / 2 < freshPenaltyReal input 0 ∅ penalty / scale penalty :=
    hlim.eventually (lt_mem_nhds (by linarith : 1 - ε / 2 < 1))
  have hbound : ∀ᶠ penalty : ℝ in atTop,
      ENNReal.ofReal ((1 - ε) * scale penalty) ≤ freshPenalty input 0 ∅ (ENNReal.ofReal penalty) - 1 := by
    filter_upwards [hratio, hscale.eventually_gt_atTop 0, hscale.eventually_ge_atTop (2 / ε)]
      with penalty hr hs hlarge
    have hf : (1 - ε / 2) * scale penalty ≤ freshPenaltyReal input 0 ∅ penalty :=
      le_of_lt ((lt_div_iff₀ hs).mp hr)
    have htwo : 2 ≤ scale penalty * ε := (div_le_iff₀ hε).mp hlarge
    have hraw : (1 - ε) * scale penalty ≤ freshPenaltyReal input 0 ∅ penalty - 1 := by
      nlinarith only [hf, htwo]
    calc
      _ ≤ ENNReal.ofReal (freshPenaltyReal input 0 ∅ penalty - 1) := ENNReal.ofReal_le_ofReal hraw
      _ = _ := by
        rw [ENNReal.ofReal_sub _ (by norm_num : (0 : ℝ) ≤ 1), ENNReal.ofReal_one]
        exact congrArg (fun value : ℝ≥0∞ => value - 1)
          (ENNReal.ofReal_toReal (freshPenalty_ne_top input 0 ∅ ENNReal.ofReal_ne_top))
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp hbound
  let cutoff : ℝ := max 1 threshold + 1
  have hc : 0 < cutoff := by dsimp [cutoff]; linarith [le_max_left (1 : ℝ) threshold]
  refine ⟨1 / cutoff, one_div_pos.mpr hc, ?_⟩
  intro δ hδ hsmall C hretained accounting
  have hinv : cutoff ≤ δ⁻¹ := by
    calc
      cutoff = 1 / (1 / cutoff) := by rw [one_div_one_div]
      _ ≤ 1 / δ := one_div_le_one_div_of_le hδ hsmall.le
      _ = _ := one_div δ
  have hthresholdInv : threshold ≤ δ⁻¹ :=
    (show threshold ≤ cutoff by dsimp [cutoff]; linarith [le_max_right (1 : ℝ) threshold]).trans hinv
  have hrelaxed := hthreshold δ⁻¹ hthresholdInv
  have hnative := initial_inverse_lower input hn C hretained accounting (ENNReal.ofReal δ)
  rw [← ENNReal.ofReal_inv_of_pos hδ] at hnative
  simpa only [scale, mul_assoc] using hrelaxed.trans hnative

end RootRetainedHead
