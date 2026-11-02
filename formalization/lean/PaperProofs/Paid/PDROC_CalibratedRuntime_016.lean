module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_015
public import PaperProofs.Paid.PDROC_CalibratedSignature_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu

namespace PDROC.CalibratedRuntime

/-- The original initial Bool selects one complete stored policy and stays
fixed at every actual clock. No local stage selector is redrawn. -/
theorem state_path_agreement (P : Parameters) (state : MultiplierState)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedSearchSeed × (P.input fee hfee).World) :
    let table := selectedTable state sample.1.1
    let summary := pathSummary P (calibratedFamily P) table P.certificate.stages P.tools
      (calibratedSuffixSeed P 0 P.certificate.stages (Nat.zero_add P.certificate.stages) sample.1.2)
      (menuSuffixWorld P P.certificate.stages P.tools 0 P.certificate.stages
        (Nat.zero_add P.certificate.stages) fee hfee sample.2)
    P.executionSignature fee hfee C .uncapped accounting (P.calibratedStateRule state) sample =
      outcomeSignature P summary.outcome ∧
    runObservationBill (P.input fee hfee) C.val .uncapped accounting (P.calibratedStateRule state) sample = summary.observation := by
  let table := selectedTable state sample.1.1
  have hr := calibratedStateRun_eq_menuRun P state fee hfee C.val .uncapped accounting sample
  have hs := menu_path_agreement P table fee hfee C accounting (sample.1.2, sample.2)
  refine ⟨?_, ?_⟩
  · exact (PDROC.CalibratedSignature.executionSignature_eq_of_same_run P fee hfee C .uncapped accounting _ _ sample (sample.1.2, sample.2) hr).trans hs.1
  · exact (PDROC.CalibratedSignature.observationBill_eq_of_same_run (P.input fee hfee) C.val .uncapped accounting _ _ sample (sample.1.2, sample.2) hr).trans hs.2

theorem multiplierSearch_path_agreement (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (steps : ℕ)
    (sample : P.CalibratedSearchSeed × (P.input fee hfee).World) :
    let state := P.multiplierSearch fee steps
    let table := selectedTable state sample.1.1
    let summary := pathSummary P (calibratedFamily P) table P.certificate.stages P.tools
      (calibratedSuffixSeed P 0 P.certificate.stages (Nat.zero_add P.certificate.stages) sample.1.2)
      (menuSuffixWorld P P.certificate.stages P.tools 0 P.certificate.stages
        (Nat.zero_add P.certificate.stages) fee hfee sample.2)
    P.executionSignature fee hfee C .uncapped accounting (P.calibratedStateRule state) sample =
      outcomeSignature P summary.outcome ∧
    runObservationBill (P.input fee hfee) C.val .uncapped accounting (P.calibratedStateRule state) sample = summary.observation :=
  state_path_agreement P (P.multiplierSearch fee steps) fee hfee C accounting sample

end PDROC.CalibratedRuntime
