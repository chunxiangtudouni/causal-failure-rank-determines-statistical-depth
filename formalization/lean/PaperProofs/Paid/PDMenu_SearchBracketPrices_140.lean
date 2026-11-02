module

public import PaperProofs.Paid.PDMenu_SearchBracketMixture_138
public import PaperProofs.Paid.PDMenu_SearchSlopeGap_137

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem searchBracket_value_le_mixture (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (lower upper : MultiplierSolve)
    (hstate : P.StateBracketCorrect fee hfee C accounting (.bracket lower upper)) :
    P.uncappedValue C accounting fee hfee ≤ ENNReal.ofReal (P.mixtureCost fee lower upper : ℝ) := by
  have hrecords := searchBracket_mixture_records P fee hfee C accounting lower upper hstate
  have h := value_le_policy (P.input fee hfee) C.val .uncapped accounting P.targetRisk (P.searchSeedLaw (.bracket lower upper))
    (P.statePolicy (.bracket lower upper) fee hfee C accounting) hrecords.2.2.2.1.le
  change P.uncappedValue C accounting fee hfee ≤
    expectedBill (P.input fee hfee) C.val .uncapped accounting (P.stateRule (.bracket lower upper))
      (P.searchSeedLaw (.bracket lower upper)) at h
  rw [hrecords.2.2.2.2] at h
  exact h

theorem searchBracket_lower_le_value (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (lower upper : MultiplierSolve)
    (hstate : P.StateBracketCorrect fee hfee C accounting (.bracket lower upper)) :
    ENNReal.ofReal (P.mixtureLower fee upper : ℝ) ≤ P.uncappedValue C accounting fee hfee := by
  obtain ⟨_, hu, hlo0, hlohi, _, _, _, _, _, _, _⟩ := hstate
  exact searchMixtureLower_le_value P fee hfee C accounting upper hu (by linarith)

end PDMenu
