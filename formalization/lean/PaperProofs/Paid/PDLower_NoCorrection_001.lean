module

public import PaperProofs.Paid.PDMenu_MajorityRisk_037
public import PaperProofs.Paid.PDLower_MajorityScale_004
public import PaperProofs.Common.NativeSeed

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDLower

theorem majority_risk_le_target (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    risk (P.input fee hf) C.val .uncapped accounting P.majorityRule (Measure.dirac ()) ≤ P.targetRisk := by
  apply (PDMenu.majority_risk_le_half P fee hf C accounting).trans
  change ENNReal.ofReal ((P.certificate.risk / 2 : ℚ) : ℝ) ≤ ENNReal.ofReal (P.certificate.risk : ℝ)
  apply ENNReal.ofReal_le_ofReal
  have h : (P.certificate.risk / 2 : ℚ) ≤ P.certificate.risk := by linarith [P.certificate.risk_pos]
  exact (Rat.cast_le (K := ℝ)).mpr h

theorem noCorrectionPolicyComparison (P : Parameters) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (fee : ℚ) (hf : 0 ≤ fee) :
    P.NoCorrectionPolicyComparison C accounting fee hf := by
  refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance,
    P.majorityPolicy fee hf C accounting, ?_, ?_, ?_⟩
  · exact PDMenu.majority_run_executions P fee hf C accounting
  · exact majority_risk_le_target P fee hf C accounting
  · exact (PDMenu.majority_expectedBill_eq_B P fee hf C accounting).le.trans (majorityBill_le_saturation P)

theorem noCorrectionValueComparison (P : Parameters) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (fee : ℚ) (hf : 0 ≤ fee) :
    P.NoCorrectionValueComparison C accounting fee hf := by
  rcases noCorrectionPolicyComparison P C accounting fee hf with
    ⟨Seed, m, ν, hν, policy, _executions, hrisk, hbill⟩
  let : MeasurableSpace Seed := m
  let : IsProbabilityMeasure ν := hν
  change value (P.input fee hf) C.val .uncapped accounting P.targetRisk ≤ 7 * P.saturationScale
  exact (value_le_policy_any_seed (P.input fee hf) C.val .uncapped accounting policy ν P.targetRisk hrisk).trans hbill

end PDLower
