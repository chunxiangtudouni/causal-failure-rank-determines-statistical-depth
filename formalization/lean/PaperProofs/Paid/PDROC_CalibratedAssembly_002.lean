module

public import PaperProofs.Paid.PDROC_CalibratedAssembly_001
public import PaperProofs.Paid.PDROC_CalibratedResources_002
public import PaperProofs.Paid.PDROC_CalibratedSelector_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open scoped ENNReal

namespace PDROC.CalibratedAssembly

theorem calibratedAlgorithmRule_of_positiveBranch (P : Parameters) (fee : ℚ)
    (positiveBranch : ¬ P.zeroChargeRisk fee ≤ P.certificate.risk) :
    P.calibratedAlgorithmRule fee = P.calibratedStateRule (P.idealSearchState fee) := by
  simp only [Parameters.calibratedAlgorithmRule, Parameters.calibratedAlgorithmCandidate,
    ite_eq_right positiveBranch, Parameters.calibratedStateRule]

/-- The original D25 and finite-search D22 guarantees imply the uncapped
calibrated algorithm guarantee, including the exact zero-charge exit.
Both original claims remain explicit premises until final instantiation. -/
theorem calibratedAlgorithm_uncapped_guarantee (P : Parameters)
    (implementation : P.CalibratedImplementationClaims)
    (termination : P.FiniteMultiplierTermination)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) :
    risk (P.input fee hfee) C.val .uncapped accounting
        (P.calibratedAlgorithmRule fee) (P.calibratedAlgorithmSeedLaw fee) ≤ P.targetRisk ∧
    expectedBill (P.input fee hfee) C.val .uncapped accounting
        (P.calibratedAlgorithmRule fee) (P.calibratedAlgorithmSeedLaw fee) ≤
      8 * P.uncappedValue C accounting fee hfee := by
  by_cases zeroBranch : P.zeroChargeRisk fee ≤ P.certificate.risk
  · have original := (termination fee hfee C accounting).1 zeroBranch
    constructor
    · rw [PDROC.CalibratedSelector.zeroBranch_risk_eq_ideal P fee hfee C .uncapped accounting zeroBranch]
      exact original.2
    · rw [PDROC.CalibratedSelector.zeroBranch_expectedBill_eq_ideal P fee hfee C .uncapped accounting zeroBranch,
        original.1]
      exact zero_le
  · have original := (termination fee hfee C accounting).2 (lt_of_not_ge zeroBranch)
    have calibrated := implementation fee hfee C accounting (P.bisectionBudget fee)
    dsimp only at calibrated
    have sourceRisk : risk (P.input fee hfee) C.val .uncapped accounting
        (P.stateRule (P.idealSearchState fee)) (P.searchSeedLaw (P.idealSearchState fee)) = P.targetRisk := by
      simpa only [Parameters.idealSearchRule, Parameters.idealSearchSeedLaw, ite_eq_right zeroBranch]
        using original.2.2.1
    have sourceBill : expectedBill (P.input fee hfee) C.val .uncapped accounting
        (P.stateRule (P.idealSearchState fee)) (P.searchSeedLaw (P.idealSearchState fee)) ≤
      2 * P.uncappedValue C accounting fee hfee := by
      simpa only [Parameters.idealSearchRule, Parameters.idealSearchSeedLaw, ite_eq_right zeroBranch]
        using original.2.2.2
    rw [calibratedAlgorithmRule_of_positiveBranch P fee zeroBranch]
    simp only [Parameters.calibratedAlgorithmSeedLaw, ite_eq_right zeroBranch]
    constructor
    · exact le_of_eq (calibrated.2.1.trans sourceRisk)
    · calc
        _ ≤ 4 * expectedBill (P.input fee hfee) C.val .uncapped accounting
            (P.stateRule (P.idealSearchState fee)) (P.searchSeedLaw (P.idealSearchState fee)) :=
          calibrated.2.2.2.2.2.1
        _ ≤ 4 * (2 * P.uncappedValue C accounting fee hfee) := mul_le_mul' le_rfl sourceBill
        _ = 8 * P.uncappedValue C accounting fee hfee := by rw [← mul_assoc]; norm_num

/-- Assemble the exact original D26 statement from D25 and original finite
search. THIS-policy H0 and original numeric caps are consumed only at native
implementation; the all-prefix resource conjunction has no qualification. -/
theorem nativeEight_of_implementation_and_termination (P : Parameters)
    (implementation : P.CalibratedImplementationClaims)
    (termination : P.FiniteMultiplierTermination) : P.CalibratedNativeEightClaims := by
  intro fee hfee C accounting
  refine ⟨PDROC.CalibratedResources.calibratedAlgorithm_resources P fee hfee C accounting, ?_⟩
  intro qualified
  let policy := PDROC.CalibratedResources.nativePolicy P fee hfee C accounting qualified
  have uncapped := calibratedAlgorithm_uncapped_guarantee P implementation termination fee hfee C accounting
  have nativeRisk : risk (P.input fee hfee) C.val .native accounting policy.rule
      (P.calibratedAlgorithmSeedLaw fee) ≤ P.targetRisk := by
    rw [PDROC.CalibratedResources.nativePolicy_risk_eq P fee hfee C accounting qualified]
    exact uncapped.1
  refine ⟨policy, rfl,
    PDROC.CalibratedResources.nativePolicy_run_eq P fee hfee C accounting qualified,
    nativeRisk, P.uncappedValue_le_nativeValue C accounting fee hfee, ?_, ?_⟩
  · exact value_le_policy (P.input fee hfee) C.val .native accounting P.targetRisk
      (P.calibratedAlgorithmSeedLaw fee) policy nativeRisk
  · rw [PDROC.CalibratedResources.nativePolicy_expectedBill_eq P fee hfee C accounting qualified]
    exact uncapped.2

end PDROC.CalibratedAssembly
