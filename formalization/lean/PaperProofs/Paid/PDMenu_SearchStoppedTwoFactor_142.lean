module

public import PaperProofs.Paid.PDMenu_SearchExactMixtureGap_141

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- The actual stopping flag implies the original two-factor full-policy
guarantee, with extended complete bills and no positivity premise. -/
theorem stoppedTwoFactor (P : Parameters) : P.StoppedTwoFactor := by
  intro fee hfee C accounting steps
  dsimp only
  intro hstop
  have hi := multiplierSearch_stateBracketCorrect P fee hfee C accounting steps
  cases hs : P.multiplierSearch fee steps with
  | exact solution =>
      rw [hs] at hi
      have he := searchExact_records P fee hfee C accounting solution hi
      refine ⟨he.1, ?_⟩
      rw [he.2.1, he.2.2]
      have htwo : (1 : ℝ≥0∞) ≤ 2 := by norm_num
      simpa only [one_mul] using mul_le_mul' htwo (le_refl (P.uncappedValue C accounting fee hfee))
  | bracket lower upper =>
      rw [hs] at hi
      have hstop' : (upper.multiplier - lower.multiplier) * P.certificate.risk ≤
          P.mixtureCost fee lower upper / 2 := by
        simpa only [hs, PaperProofs.Paid.Parameters.searchStopped, decide_eq_true_eq] using hstop
      have hm := searchBracket_mixture_records P fee hfee C accounting lower upper hi
      have hg := searchBracket_gapBounds P fee hfee C accounting lower upper hi
      have hprice := searchBracket_lower_le_value P fee hfee C accounting lower upper hi
      have hrat : P.mixtureCost fee lower upper ≤ 2 * P.mixtureLower fee upper := by
        linarith [hg.2.1, hg.2.2]
      refine ⟨hm.2.2.2.1, ?_⟩
      rw [hm.2.2.2.2]
      calc
        _ ≤ ENNReal.ofReal ((2 * P.mixtureLower fee upper : ℚ) : ℝ) :=
          ENNReal.ofReal_le_ofReal (by exact_mod_cast hrat)
        _ = 2 * ENNReal.ofReal (P.mixtureLower fee upper : ℝ) := by
          rw [Rat.cast_mul, Rat.cast_ofNat, ENNReal.ofReal_mul (by norm_num)]
          norm_num
        _ ≤ 2 * P.uncappedValue C accounting fee hfee := mul_le_mul' le_rfl hprice

end PDMenu
