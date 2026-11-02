module

public import PaperProofs.Paid.PDMenu_SearchInitialBracket_132

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem searchInitial_stateBracketCorrect (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    P.StateBracketCorrect fee hfee C accounting (P.initialMultiplierState fee) := by
  have h := majorityInitialBracket P fee hfee C accounting
  have hl := searchSolveStats P fee hfee 0
  have hu := searchSolveStats P fee hfee P.Lambda
  refine ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, le_rfl, P.Lambda_pos, le_rfl, ?_, ?_, hu.2.1, hl.2.2, hl.1, hu.1⟩
  · rw [solveZero_risk]
    linarith [P.certificate.risk_le]
  · exact (searchUpper_risk_le_three_quarters P fee hfee C accounting).trans (by linarith [P.certificate.risk_pos])

theorem searchBisect_stateBracketCorrect (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (state : MultiplierState)
    (hstate : P.StateBracketCorrect fee hfee C accounting state) :
    P.StateBracketCorrect fee hfee C accounting (P.bisectMultiplier fee state) := by
  cases state with
  | exact solution => exact hstate
  | bracket lower upper =>
    obtain ⟨hl, hu, hlo0, hlohi, hhiCap, hrl, hru, hru0, hrl1, hcl, hcu⟩ := hstate
    let middle := P.solveMultiplier fee ((lower.multiplier + upper.multiplier) / 2)
    have hm0 : 0 ≤ (lower.multiplier + upper.multiplier) / 2 := by linarith
    have hmΛ : (lower.multiplier + upper.multiplier) / 2 ≤ P.Lambda := by linarith
    have hml : lower.multiplier < middle.multiplier := by
      change lower.multiplier < (lower.multiplier + upper.multiplier) / 2
      linarith
    have hmu : middle.multiplier < upper.multiplier := by
      change (lower.multiplier + upper.multiplier) / 2 < upper.multiplier
      linarith
    have hm := searchSolveCorrect P fee hfee C accounting _ hm0 hmΛ
    have hstats := searchSolveStats P fee hfee ((lower.multiplier + upper.multiplier) / 2)
    change P.StateBracketCorrect fee hfee C accounting
      (if P.solveRisk middle = P.certificate.risk then .exact middle else
        if P.certificate.risk < P.solveRisk middle then .bracket middle upper else .bracket lower middle)
    by_cases he : P.solveRisk middle = P.certificate.risk
    · rw [ite_eq_left he]
      exact ⟨hm, hm0, hmΛ, he⟩
    · rw [ite_eq_right he]
      by_cases hh : P.certificate.risk < P.solveRisk middle
      · rw [ite_eq_left hh]
        exact ⟨hm, hu, hm0, hmu, hhiCap, hh, hru, hru0, hstats.2.2, hstats.1, hcu⟩
      · rw [ite_eq_right hh]
        exact ⟨hl, hm, hlo0, hml, hmΛ, hrl, le_of_not_gt hh, hstats.2.1, hrl1, hcl, hstats.1⟩

theorem searchStep_stateBracketCorrect (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (state : MultiplierState)
    (hstate : P.StateBracketCorrect fee hfee C accounting state) :
    P.StateBracketCorrect fee hfee C accounting (P.multiplierStep fee state) := by
  unfold PaperProofs.Paid.Parameters.multiplierStep
  split_ifs
  · exact hstate
  · exact searchBisect_stateBracketCorrect P fee hfee C accounting state hstate

theorem multiplierSearch_stateBracketCorrect (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (steps : ℕ) :
    P.StateBracketCorrect fee hfee C accounting (P.multiplierSearch fee steps) := by
  induction steps with
  | zero => exact searchInitial_stateBracketCorrect P fee hfee C accounting
  | succ steps ih => exact searchStep_stateBracketCorrect P fee hfee C accounting _ ih

end PDMenu
