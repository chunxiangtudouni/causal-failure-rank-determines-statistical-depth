module

public import PaperProofs.Paid.PDMenu_SearchFloorBudget_154

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem idealSearchState_stopped (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (hgap : P.certificate.risk < P.zeroChargeRisk fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) :
    P.searchStopped fee (P.idealSearchState fee) = true := by
  by_contra hn
  have hwidth := multiplierSearch_width_of_not_stopped P fee hfee C accounting
    (P.bisectionBudget fee) hn
  have hfloor := PDROC.ZeroChargeLower.Transport.positiveValueFloor_pos P fee hfee hgap
  have hbudget := bisectionBudget_width P fee hfloor
  have hi := multiplierSearch_stateBracketCorrect P fee hfee C accounting (P.bisectionBudget fee)
  have hvalue := zeroCharge_value_floor P fee hfee hgap C accounting
  cases hs : P.idealSearchState fee with
  | exact solution =>
      exact hn (by simp only [hs, PaperProofs.Paid.Parameters.searchStopped])
  | bracket lower upper =>
      change P.StateBracketCorrect fee hfee C accounting (P.idealSearchState fee) at hi
      rw [hs] at hi
      change multiplierWidth (P.idealSearchState fee) ≤ _ at hwidth
      rw [hs] at hwidth
      have hm := searchBracket_mixture_records P fee hfee C accounting lower upper hi
      have hv := searchBracket_value_le_mixture P fee hfee C accounting lower upper hi
      obtain ⟨_, _, _, _, _, _, _, _, _, hcl, hcu⟩ := hi
      have hU0 : 0 ≤ P.mixtureCost fee lower upper := by
        exact add_nonneg (mul_nonneg hm.1 hcl) (mul_nonneg (sub_nonneg.mpr hm.2.1) hcu)
      have hfloorU : P.positiveValueFloor fee ≤ P.mixtureCost fee lower upper := by
        have h := hvalue.trans hv
        have hreal : (P.positiveValueFloor fee:ℝ) ≤ (P.mixtureCost fee lower upper:ℝ) :=
          (ENNReal.ofReal_le_ofReal_iff (by exact_mod_cast hU0)).mp h
        exact_mod_cast hreal
      have hstop : (upper.multiplier-lower.multiplier)*P.certificate.risk ≤
          P.mixtureCost fee lower upper/2 := by
        calc
          _ ≤ (P.Lambda/(2:ℚ)^P.bisectionBudget fee)*P.certificate.risk :=
            mul_le_mul_of_nonneg_right hwidth P.certificate.risk_pos.le
          _ ≤ P.positiveValueFloor fee/2 := hbudget
          _ ≤ P.mixtureCost fee lower upper/2 := div_le_div_of_nonneg_right hfloorU (by norm_num)
      exact hn (by simp only [hs, PaperProofs.Paid.Parameters.searchStopped, decide_eq_true_eq]; exact hstop)

end PDMenu
