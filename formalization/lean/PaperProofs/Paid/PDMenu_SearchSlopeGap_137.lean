module

public import PaperProofs.Paid.PDMenu_SearchWeakDuality_136

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem searchBracket_slopeBounds (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (lower upper : MultiplierSolve)
    (hstate : P.StateBracketCorrect fee hfee C accounting (.bracket lower upper)) :
    -upper.multiplier ≤ (P.solveCost fee lower - P.solveCost fee upper) / (P.solveRisk lower - P.solveRisk upper) ∧
      (P.solveCost fee lower - P.solveCost fee upper) / (P.solveRisk lower - P.solveRisk upper) ≤ -lower.multiplier := by
  obtain ⟨hl, hu, hlo0, hlohi, _, hrl, hru, hru0, _, hcl, hcu⟩ := hstate
  have hhi0 : 0 ≤ upper.multiplier := by linarith
  have hrl0 : 0 ≤ P.solveRisk lower := by linarith [P.certificate.risk_pos]
  have hloOpt := searchCrossObjective P fee hfee C accounting lower upper hl hu hlo0 hcu hru0
  have hhiOpt := searchCrossObjective P fee hfee C accounting upper lower hu hl hhi0 hcl hrl0
  have hd : 0 < P.solveRisk lower - P.solveRisk upper := by linarith
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    nlinarith

theorem searchBracket_gapIdentity (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) :
    P.mixtureCost fee lower upper - P.mixtureLower fee upper =
      (P.certificate.risk - P.solveRisk upper) *
        ((P.solveCost fee lower - P.solveCost fee upper) / (P.solveRisk lower - P.solveRisk upper) + upper.multiplier) := by
  dsimp only [PaperProofs.Paid.Parameters.mixtureCost, PaperProofs.Paid.Parameters.mixtureLower,
    PaperProofs.Paid.Parameters.mixtureWeight]
  rw [searchRecord_objective]
  ring

theorem searchBracket_gapBounds (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (lower upper : MultiplierSolve)
    (hstate : P.StateBracketCorrect fee hfee C accounting (.bracket lower upper)) :
    0 ≤ P.mixtureCost fee lower upper - P.mixtureLower fee upper ∧
      P.mixtureCost fee lower upper - P.mixtureLower fee upper ≤
        (upper.multiplier - lower.multiplier) * (P.certificate.risk - P.solveRisk upper) ∧
      (upper.multiplier - lower.multiplier) * (P.certificate.risk - P.solveRisk upper) ≤
        (upper.multiplier - lower.multiplier) * P.certificate.risk := by
  have hs := searchBracket_slopeBounds P fee hfee C accounting lower upper hstate
  obtain ⟨_, _, _, hlohi, _, _, hru, hru0, _, _, _⟩ := hstate
  have ht : 0 ≤ P.certificate.risk - P.solveRisk upper := sub_nonneg.mpr hru
  have hdiff : 0 ≤ upper.multiplier - lower.multiplier := sub_nonneg.mpr hlohi.le
  refine ⟨?_, ?_, ?_⟩
  · rw [searchBracket_gapIdentity]
    exact mul_nonneg ht (by linarith [hs.1])
  · rw [searchBracket_gapIdentity]
    calc
      _ ≤ (P.certificate.risk - P.solveRisk upper) * (upper.multiplier - lower.multiplier) :=
        mul_le_mul_of_nonneg_left (by linarith [hs.2]) ht
      _ = _ := mul_comm _ _
  · nlinarith [mul_nonneg hdiff hru0]

end PDMenu
