module

public import PaperProofs.Paid.PDMenu_SearchMixtureRecords_135
public import PaperProofs.Paid.PDMenu_SearchBracketInvariant_134

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem searchWeighted_record (w a b : ℚ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal (w : ℝ) * ENNReal.ofReal (a : ℝ) +
      ENNReal.ofReal (1 - (w : ℝ)) * ENNReal.ofReal (b : ℝ) =
        ENNReal.ofReal ((w * a + (1 - w) * b : ℚ) : ℝ) := by
  have h := PDMenuNativeValue.menuWeightedObjectiveENN 0 w b a le_rfl hw0 hw1 hb ha
  simp only [zero_add, Rat.cast_zero, ENNReal.ofReal_zero] at h
  calc
    _ = ENNReal.ofReal (1 - (w : ℝ)) * ENNReal.ofReal (b : ℝ) + ENNReal.ofReal (w : ℝ) * ENNReal.ofReal (a : ℝ) := add_comm _ _
    _ = ENNReal.ofReal (((1 - w) * b + w * a : ℚ) : ℝ) := h.symm
    _ = _ := congrArg ENNReal.ofReal (by push_cast; ring)

theorem searchMixtureRisk_record (P : Parameters) (lower upper : MultiplierSolve)
    (hl : P.certificate.risk < P.solveRisk lower) (hu : P.solveRisk upper ≤ P.certificate.risk) :
    P.mixtureWeight lower upper * P.solveRisk lower +
      (1 - P.mixtureWeight lower upper) * P.solveRisk upper = P.certificate.risk := by
  have hd : P.solveRisk lower - P.solveRisk upper ≠ 0 := by linarith
  unfold PaperProofs.Paid.Parameters.mixtureWeight
  field_simp [hd]; ring

/-- Actual initial mixture risk and full actual-bill means at an arbitrary
valid bracket, with the original clipping proved nonbinding. -/
theorem searchBracket_mixture_records (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (lower upper : MultiplierSolve)
    (hstate : P.StateBracketCorrect fee hfee C accounting (.bracket lower upper)) :
    0 ≤ P.mixtureWeight lower upper ∧ P.mixtureWeight lower upper ≤ 1 ∧
      (P.clippedMixtureWeight lower upper).val = (P.mixtureWeight lower upper : ℝ) ∧
      risk (P.input fee hfee) C.val .uncapped accounting (P.stateRule (.bracket lower upper)) (P.searchSeedLaw (.bracket lower upper)) = P.targetRisk ∧
      expectedBill (P.input fee hfee) C.val .uncapped accounting (P.stateRule (.bracket lower upper)) (P.searchSeedLaw (.bracket lower upper)) =
        ENNReal.ofReal (P.mixtureCost fee lower upper : ℝ) := by
  obtain ⟨hl, hu, _, _, _, hrl, hru, hru0, _, hcl, hcu⟩ := hstate
  have hw := P.mixtureWeight_mem_of_bracket lower upper hrl hru
  have hclip := P.clippedMixtureWeight_eq lower upper hw.1 hw.2
  have hrl0 : 0 ≤ P.solveRisk lower := by linarith [P.certificate.risk_pos]
  refine ⟨hw.1, hw.2, hclip, ?_, ?_⟩
  · rw [searchBracket_risk P fee hfee C .uncapped accounting lower upper, hl.2.2.1, hu.2.2.1, hclip,
      searchWeighted_record _ _ _ hw.1 hw.2 hrl0 hru0,
      searchMixtureRisk_record P lower upper hrl hru]
    rfl
  · rw [searchBracket_expectedBill P fee hfee C .uncapped accounting lower upper, hl.2.1, hu.2.1, hclip,
      searchWeighted_record _ _ _ hw.1 hw.2 hcl hcu]
    rfl

end PDMenu
