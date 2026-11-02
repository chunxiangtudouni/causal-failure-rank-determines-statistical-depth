module

public import PaperProofs.Paid.PDMenu_SearchStoppedTwoFactor_142

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

def multiplierWidth : MultiplierState → ℚ
  | .exact _ => 0
  | .bracket lower upper => upper.multiplier-lower.multiplier

theorem multiplierWidth_nonneg (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (state : MultiplierState)
    (hstate : P.StateBracketCorrect fee hfee C accounting state) : 0 ≤ multiplierWidth state := by
  cases state with
  | exact => exact le_rfl
  | bracket lower upper => exact sub_nonneg.mpr hstate.2.2.2.1.le

theorem multiplierWidth_bisect_le_half (P : Parameters) (fee : ℚ) (state : MultiplierState)
    (hw : 0 ≤ multiplierWidth state) :
    multiplierWidth (P.bisectMultiplier fee state) ≤ multiplierWidth state/2 := by
  cases state with
  | exact => simp only [PaperProofs.Paid.Parameters.bisectMultiplier, multiplierWidth, zero_div, le_refl]
  | bracket lower upper =>
      unfold PaperProofs.Paid.Parameters.bisectMultiplier
      dsimp only
      split_ifs
      · exact div_nonneg hw (by norm_num)
      · change upper.multiplier-(lower.multiplier+upper.multiplier)/2 ≤ (upper.multiplier-lower.multiplier)/2
        linarith
      · change (lower.multiplier+upper.multiplier)/2-lower.multiplier ≤ (upper.multiplier-lower.multiplier)/2
        linarith

/-- Unstopped actual search has halved its original rational width once
per actual bisection. Stopped states are retained by the original code. -/
theorem multiplierSearch_width_of_not_stopped (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    ∀ steps, P.searchStopped fee (P.multiplierSearch fee steps) ≠ true →
      multiplierWidth (P.multiplierSearch fee steps) ≤ P.Lambda/(2:ℚ)^steps := by
  intro steps
  induction steps with
  | zero => intro _; simp [PaperProofs.Paid.Parameters.multiplierSearch, PaperProofs.Paid.Parameters.initialMultiplierState,
      multiplierWidth, PaperProofs.Paid.Parameters.solveMultiplier]
  | succ steps ih =>
      intro hnot
      by_cases hp : P.searchStopped fee (P.multiplierSearch fee steps) = true
      · have he : P.multiplierSearch fee (steps+1) = P.multiplierSearch fee steps := by
          simp only [PaperProofs.Paid.Parameters.multiplierSearch, PaperProofs.Paid.Parameters.multiplierStep, hp, ite_true]
        exact False.elim (hnot (by rw [he]; exact hp))
      · have he : P.multiplierSearch fee (steps+1) = P.bisectMultiplier fee (P.multiplierSearch fee steps) := by
          simp only [PaperProofs.Paid.Parameters.multiplierSearch, PaperProofs.Paid.Parameters.multiplierStep, ite_eq_right hp]
        rw [he]
        calc
          _ ≤ multiplierWidth (P.multiplierSearch fee steps)/2 :=
            multiplierWidth_bisect_le_half P fee _ (multiplierWidth_nonneg P fee hfee C accounting _
              (multiplierSearch_stateBracketCorrect P fee hfee C accounting steps))
          _ ≤ (P.Lambda/(2:ℚ)^steps)/2 := div_le_div_of_nonneg_right (ih hp) (by norm_num)
          _ = P.Lambda/(2:ℚ)^(steps+1) := by rw [pow_succ, div_mul_eq_div_div]

end PDMenu
