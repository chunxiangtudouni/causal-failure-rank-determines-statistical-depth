module

public import PaperProofs.Paid.PDLower_FreeSqueeze_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open Filter
open scoped ENNReal Topology
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Structure
open PaperProofs.Statistics PaperProofs.Paid

namespace PDLower

theorem log_saturation_uniform_cutoff (stages : ℕ) (hstages : 0 < stages)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ delta : ℝ, 0 < delta → delta < cutoff →
      (1 - epsilon) * Real.log delta⁻¹ ≤ Real.log (1 + (stages : ℝ) / delta) ∧
      Real.log (1 + (stages : ℝ) / delta) ≤ (1 + epsilon) * Real.log delta⁻¹ := by
  have hscale : 0 < (stages : ℝ) + 1 := by positivity
  have hratio := (iteratedLog_scale_div_tendsto_one 1 (by norm_num)
    ((stages : ℝ) + 1) hscale).eventually
      (eventually_lt_nhds (by linarith : (1 : ℝ) < 1 + epsilon))
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp hratio
  let large := max threshold 2
  have hlarge : 0 < large := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨1 / large, one_div_pos.mpr hlarge, ?_⟩
  intro delta hdelta hcutoff
  have hinverse : large < delta⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ hdelta).mpr
    have hmul := (lt_div_iff₀ hlarge).mp hcutoff
    nlinarith
  have htwo : 2 ≤ delta⁻¹ := (le_max_right _ _).trans hinverse.le
  have hone : (1 : ℝ) < delta⁻¹ := lt_of_lt_of_le (by norm_num) htwo
  have hlog : 0 < Real.log delta⁻¹ := Real.log_pos hone
  have hstagesReal : (1 : ℝ) ≤ stages := by exact_mod_cast hstages
  have hleftInput : delta⁻¹ ≤ 1 + (stages : ℝ) / delta := by
    rw [div_eq_mul_inv]
    have hmul := mul_le_mul_of_nonneg_right hstagesReal (inv_pos.mpr hdelta).le
    nlinarith only [hmul]
  have hrightInput : 1 + (stages : ℝ) / delta ≤ ((stages : ℝ) + 1) * delta⁻¹ := by
    rw [div_eq_mul_inv]
    nlinarith only [htwo]
  have hlowerLog : Real.log delta⁻¹ ≤ Real.log (1 + (stages : ℝ) / delta) :=
    Real.log_le_log (inv_pos.mpr hdelta) hleftInput
  have hupperLog : Real.log (1 + (stages : ℝ) / delta) ≤
      Real.log (((stages : ℝ) + 1) * delta⁻¹) :=
    Real.log_le_log (lt_of_lt_of_le (inv_pos.mpr hdelta) hleftInput) hrightInput
  have hratioInput : threshold ≤ delta⁻¹ := (le_max_left _ _).trans hinverse.le
  have hratioBound := hthreshold delta⁻¹ hratioInput
  change Real.log (((stages : ℝ) + 1) * delta⁻¹) / Real.log delta⁻¹ < 1 + epsilon
    at hratioBound
  have hscaled := ((div_lt_iff₀ hlog).mp hratioBound).le
  constructor
  · have hfirst : (1 - epsilon) * Real.log delta⁻¹ ≤ Real.log delta⁻¹ := by
      nlinarith only [hlog, hepsilon, mul_pos hepsilon hlog]
    exact hfirst.trans hlowerLog
  · exact hupperLog.trans hscaled

theorem zeroToolsStructuralSaturation (pool : FixedSharedPool) : pool.ZeroToolsStructuralSaturation := by
  intro htools epsilon hepsilon _hepsilonOne
  obtain ⟨cutoff, hcutoff, hlogs⟩ :=
    log_saturation_uniform_cutoff pool.stages pool.stages_pos epsilon hepsilon
  refine ⟨cutoff, hcutoff, ?_⟩
  intro delta hdelta _hsmall hdeltaCutoff
  have hdeltaReal : (0 : ℝ) < delta := by exact_mod_cast hdelta
  obtain ⟨hlower, hupper⟩ := hlogs (delta : ℝ) hdeltaReal hdeltaCutoff
  have hfactor : 0 ≤ pool.channel.a * (pool.stages : ℝ) :=
    mul_nonneg pool.channel.a_pos.le (Nat.cast_nonneg _)
  have hscale : pool.structuralScaleReal delta =
      pool.channel.a * (pool.stages : ℝ) * Real.log (delta : ℝ)⁻¹ := by
    simp only [FixedSharedPool.structuralScaleReal, htools, Nat.sub_zero, iteratedLog]
  rw [hscale, FixedSharedPool.saturationScale]
  constructor
  · apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc, mul_left_comm (1 - epsilon)] using
      mul_le_mul_of_nonneg_left hlower hfactor
  · apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc, mul_left_comm (1 + epsilon)] using
      mul_le_mul_of_nonneg_left hupper hfactor

end PDLower
