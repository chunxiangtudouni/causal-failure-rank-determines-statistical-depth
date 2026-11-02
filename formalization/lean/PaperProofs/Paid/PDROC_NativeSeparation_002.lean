module

public import PaperProofs.Paid.PDROC_NativeSeparation_001
public import PaperProofs.Paid.PDROC_Separation_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

/-- The exact remaining fixed-backend obligation suffices for D29. This
uses the original qualification and original fixed script; the resource
field and value inequalities of D26 are not separate helper assumptions. -/
theorem nativeSeparationClaims_of_fixedEight_witness (P : Parameters)
    (hbackend : ∀ (fee : ℚ) (hf : 0 ≤ fee) (C : P.PaymentContract)
      (accounting : NormalAccounting P.sharedInstance),
      P.CalibratedOriginalQualification fee hf C accounting →
      ∃ policy : Policy (P.input fee hf) C.val .native accounting P.CalibratedSearchSeed,
        policy.rule = P.calibratedAlgorithmRule fee ∧
        (∀ sample n, run (P.input fee hf) C.val .native accounting policy.rule sample n =
          run (P.input fee hf) C.val .uncapped accounting (P.calibratedAlgorithmRule fee) sample n) ∧
        risk (P.input fee hf) C.val .native accounting policy.rule (P.calibratedAlgorithmSeedLaw fee) ≤ P.targetRisk ∧
        expectedBill (P.input fee hf) C.val .native accounting policy.rule (P.calibratedAlgorithmSeedLaw fee) ≤
          8 * P.uncappedValue C accounting fee hf) :
    P.NativeSeparationClaims := by
  intro fee hf C accounting
  refine ⟨nativeSeparation_lower P C accounting fee hf, ?_⟩
  intro qualification
  obtain ⟨policy, hrule, hruns, hrisk, hbill⟩ := hbackend fee hf C accounting qualification
  have hsand := nativeSeparation_feasible_sandwich P C accounting fee hf policy
    (P.calibratedAlgorithmSeedLaw fee) hrisk hbill
  refine ⟨?_, policy, hrule, hruns, hrisk, hsand.1, hsand.2.1, hbill⟩
  exact nativeSeparation_upper_of_eight P C accounting fee hf (hsand.2.1.trans hbill)
    (uncappedSeparationUpper P C accounting fee hf)

/-- Explicit conditional assembly of the exact original D29. The sole
unproved backend input is the original complete D26 target; it is not a
new qualification and this theorem does not assert D26 or D29 outright. -/
theorem nativeSeparationClaims_of_calibratedNativeEight (P : Parameters)
    (height : P.CalibratedNativeEightClaims) : P.NativeSeparationClaims := by
  apply nativeSeparationClaims_of_fixedEight_witness P
  intro fee hf C accounting qualification
  obtain ⟨policy, hrule, hruns, hrisk, _hrelax, _hvalue, hbill⟩ := (height fee hf C accounting).2 qualification
  exact ⟨policy, hrule, hruns, hrisk, hbill⟩

end PDROC
