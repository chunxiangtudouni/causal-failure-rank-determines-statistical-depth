module

public import PaperProofs.Paid.PDMenu_SearchWidth_153
public import PaperProofs.Paid.PDROC_ZeroChargeLower_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem zeroCharge_value_floor (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (hgap : P.certificate.risk < P.zeroChargeRisk fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) :
    ENNReal.ofReal (P.positiveValueFloor fee:ℝ) ≤ P.uncappedValue C accounting fee hfee := by
  change _ ≤ value (P.input fee hfee) C.val .uncapped accounting P.targetRisk
  unfold value
  refine le_iInf fun Seed => le_iInf fun m => ?_
  let : MeasurableSpace Seed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  exact PDROC.ZeroChargeLower.originalPositiveCostFloor P fee hfee hgap C accounting .uncapped Seed m ν hν policy.val policy.property

/-- The literal Nat.clog/ceil budget bounds the exact rational bisection
width, including budgets zero and without an approximate real logarithm. -/
theorem bisectionBudget_width (P : Parameters) (fee : ℚ)
    (hfloor : 0 < P.positiveValueFloor fee) :
    (P.Lambda/(2:ℚ)^P.bisectionBudget fee)*P.certificate.risk ≤ P.positiveValueFloor fee/2 := by
  have hn := Nat.le_pow_clog (by norm_num : 1 < (2:ℕ))
    ⌈2*P.Lambda*P.certificate.risk/P.positiveValueFloor fee⌉₊
  have hc : 2*P.Lambda*P.certificate.risk/P.positiveValueFloor fee ≤
      (⌈2*P.Lambda*P.certificate.risk/P.positiveValueFloor fee⌉₊ : ℕ) := Nat.le_ceil _
  have hp : 2*P.Lambda*P.certificate.risk/P.positiveValueFloor fee ≤ (2:ℚ)^P.bisectionBudget fee := by
    apply hc.trans
    exact_mod_cast hn
  have hp0 : (0:ℚ) < 2^P.bisectionBudget fee := pow_pos (by norm_num) _
  have hmul := (div_le_iff₀ hfloor).mp hp
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hp0).mpr
  nlinarith

end PDMenu
