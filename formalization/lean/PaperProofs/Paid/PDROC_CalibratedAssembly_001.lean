module

public import PaperProofs.Paid.PDROC_CalibratedSignature_003
public import PaperProofs.Paid.PDMenu_SearchExactMixtureGap_141

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open scoped ENNReal

namespace PDROC.CalibratedAssembly

/-- The original exact-mixture theorem identifies the complete source bill
with the actual reachable state's recorded rational cost. -/
theorem state_expectedBill_eq_recordedCost (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (steps : ℕ) :
    expectedBill (P.input fee hfee) C.val .uncapped accounting
        (P.stateRule (P.multiplierSearch fee steps)) (P.searchSeedLaw (P.multiplierSearch fee steps)) =
      ENNReal.ofReal (P.recordedStateCost fee (P.multiplierSearch fee steps) : ℝ) := by
  have records := PDMenu.exactMixtureAndGap P fee hfee C accounting steps
  dsimp only at records
  cases state : P.multiplierSearch fee steps with
  | exact solution =>
      simp only [state] at records
      exact records.2.2.1
  | bracket lower upper =>
      simp only [state] at records
      exact records.2.2.2.2.2.1

/-- Logical assembly of all seven original D25 fields. The two remaining
inputs are explicitly the actual-controller signature law and observation
comparison; this helper does not assert that those inputs have been proved. -/
theorem implementation_of_state_laws (P : Parameters)
    (laws : ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
      (accounting : NormalAccounting P.sharedInstance) (steps : ℕ),
      let state := P.multiplierSearch fee steps
      P.executionSignatureLaw fee hfee C .uncapped accounting
          (P.calibratedStateRule state) (P.calibratedStateSeedLaw state) =
        P.executionSignatureLaw fee hfee C .uncapped accounting (P.stateRule state) (P.searchSeedLaw state) ∧
      expectedObservationBill (P.input fee hfee) C.val .uncapped accounting
          (P.calibratedStateRule state) (P.calibratedStateSeedLaw state) ≤
        4 * expectedObservationBill (P.input fee hfee) C.val .uncapped accounting
          (P.stateRule state) (P.searchSeedLaw state)) :
    P.CalibratedImplementationClaims := by
  intro fee hfee C accounting steps
  dsimp only
  obtain ⟨same, observations⟩ := laws fee hfee C accounting steps
  let state := P.multiplierSearch fee steps
  let actual := P.calibratedStatePolicy state fee hfee C accounting
  let source := P.statePolicy state fee hfee C accounting
  have riskEq := PDROC.CalibratedSignature.risk_eq_of_signatureLaw P fee hfee C .uncapped accounting
    actual (P.calibratedStateSeedLaw state) source (P.searchSeedLaw state) same
  have correctionLawEq := PDROC.CalibratedSignature.correctionBillLaw_eq_of_signatureLaw
    P fee hfee C .uncapped accounting actual (P.calibratedStateSeedLaw state)
    source (P.searchSeedLaw state) same
  have correctionEq := PDROC.CalibratedSignature.expectedCorrectionBill_eq_of_signatureLaw
    P fee hfee C .uncapped accounting actual (P.calibratedStateSeedLaw state)
    source (P.searchSeedLaw state) same
  have bill := PDROC.CalibratedSignature.expectedBill_le_four_of_signatureLaw
    P fee hfee C .uncapped accounting actual (P.calibratedStateSeedLaw state)
    source (P.searchSeedLaw state) same observations
  refine ⟨same, riskEq, correctionLawEq, correctionEq, observations, bill, ?_⟩
  exact bill.trans_eq (congrArg (fun cost : ℝ≥0∞ => 4 * cost)
    (state_expectedBill_eq_recordedCost P fee hfee C accounting steps))

end PDROC.CalibratedAssembly
