module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_016
public import PaperProofs.Paid.PDROC_CalibratedLaw_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu

namespace PDROC.CalibratedRuntime

theorem calibratedRawRecord_eq_crop (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (sample : P.CalibratedMenuSeed × (P.input fee hfee).World) :
    PDROC.CalibratedLaw.calibratedRawRecord P table fee hfee sample =
      pathSummary P (calibratedFamily P) table P.certificate.stages P.tools
        (calibratedSuffixSeed P 0 P.certificate.stages (Nat.zero_add P.certificate.stages) sample.1)
        (menuSuffixWorld P P.certificate.stages P.tools 0 P.certificate.stages
          (Nat.zero_add P.certificate.stages) fee hfee sample.2) := by
  have hseed : calibratedSuffixSeed P 0 P.certificate.stages (Nat.zero_add P.certificate.stages) sample.1 =
      PDROC.CalibratedLaw.calibratedSeedFinView P sample.1 := by
    rw [calibratedSuffixSeed_root]
    funext i
    exact (PDROC.CalibratedLaw.calibratedSeedFinView_apply P sample.1 i).symm
  have hworld := menuSuffixWorld_root P P.certificate.stages P.tools fee hfee sample.2
  change pathSummary P (calibratedFamily P) table P.certificate.stages P.tools
    (PDROC.CalibratedLaw.calibratedSeedFinView P sample.1)
    (menuWorldFinEquiv P P.certificate.stages P.tools fee hfee sample.2) = _
  exact congrArg₂ (fun seed world => pathSummary P (calibratedFamily P) table P.certificate.stages P.tools seed world)
    hseed.symm hworld.symm

/-- All-path original-run refinement to the unique original-seed/world
record used by the distribution and expectation proofs. -/
theorem calibratedMenu_native_agreement (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedMenuSeed × (P.input fee hfee).World) :
    P.executionSignature fee hfee C .uncapped accounting (menuRule P table) sample =
      outcomeSignature P (PDROC.CalibratedLaw.calibratedRawRecord P table fee hfee sample).outcome ∧
    runObservationBill (P.input fee hfee) C.val .uncapped accounting (menuRule P table) sample =
      (PDROC.CalibratedLaw.calibratedRawRecord P table fee hfee sample).observation := by
  rw [calibratedRawRecord_eq_crop]
  exact menu_path_agreement P table fee hfee C accounting sample

theorem calibratedState_native_agreement (P : Parameters) (state : MultiplierState)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedSearchSeed × (P.input fee hfee).World) :
    let record := PDROC.CalibratedLaw.calibratedRawRecord P (selectedTable state sample.1.1)
      fee hfee (sample.1.2, sample.2)
    P.executionSignature fee hfee C .uncapped accounting (P.calibratedStateRule state) sample =
      outcomeSignature P record.outcome ∧
    runObservationBill (P.input fee hfee) C.val .uncapped accounting (P.calibratedStateRule state) sample = record.observation := by
  dsimp only
  rw [calibratedRawRecord_eq_crop]
  exact state_path_agreement P state fee hfee C accounting sample

/-- The original D25 runtime call: arbitrary actual multiplier-search
iteration count, the original state rule, and its one initial selector. -/
theorem multiplierSearch_native_agreement (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (steps : ℕ)
    (sample : P.CalibratedSearchSeed × (P.input fee hfee).World) :
    let state := P.multiplierSearch fee steps
    let record := PDROC.CalibratedLaw.calibratedRawRecord P (selectedTable state sample.1.1)
      fee hfee (sample.1.2, sample.2)
    P.executionSignature fee hfee C .uncapped accounting (P.calibratedStateRule state) sample =
      outcomeSignature P record.outcome ∧
    runObservationBill (P.input fee hfee) C.val .uncapped accounting (P.calibratedStateRule state) sample = record.observation :=
  calibratedState_native_agreement P (P.multiplierSearch fee steps) fee hfee C accounting sample

end PDROC.CalibratedRuntime
