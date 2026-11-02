module

public import PaperProofs.Paid.PDROC_CalibratedLaw_012
public import PaperProofs.Paid.PDROC_CalibratedRuntime_017
public import PaperProofs.Paid.PDROC_CalibratedIdeal_008
public import PaperProofs.Paid.PDMenu_SearchExactMixtureGap_141

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Statistics
open scoped ENNReal

namespace PDROC.CalibratedLaw

open PDROC.CalibratedRuntime

theorem multiplierSearch_selectedTable_levelsValid (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (steps : ℕ) (branch : Bool) :
    TableLevelsValid P (selectedTable (P.multiplierSearch fee steps) branch) := by
  have correct := PDMenu.multiplierSearch_stateBracketCorrect P fee hfee C accounting steps
  cases hs : P.multiplierSearch fee steps with
  | exact solution =>
    simp only [hs] at correct ⊢
    change TableLevelsValid P solution.table
    rw [correct.1.1]
    exact solveMenuTable_levelsValid P fee solution.multiplier P.certificate.stages P.tools
  | bracket lower upper =>
    simp only [hs] at correct ⊢
    cases branch with
    | false =>
      change TableLevelsValid P upper.table
      rw [correct.2.1.1]
      exact solveMenuTable_levelsValid P fee upper.multiplier P.certificate.stages P.tools
    | true =>
      change TableLevelsValid P lower.table
      rw [correct.1.1]
      exact solveMenuTable_levelsValid P fee lower.multiplier P.certificate.stages P.tools

theorem idealState_native_agreement_ae (P : Parameters) (state : MultiplierState)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (P.searchSeedLaw state),
      P.executionSignature fee hfee C .uncapped accounting (P.stateRule state) sample =
        outcomeSignature P (idealSelectedRecord P (selectedTable state) fee hfee sample).outcome ∧
      runObservationBill (P.input fee hfee) C.val .uncapped accounting (P.stateRule state) sample =
        (idealSelectedRecord P (selectedTable state) fee hfee sample).observation := by
  have branches (branch : Bool) :=
    PDROC.CalibratedIdeal.ideal_run_summary_ae P (selectedTable state branch) fee hfee C accounting
  have allBranches := initialSelector_ae (menuSeedLaw P.certificate.stages P.tools)
    (P.input fee hfee).worldLaw (P.stateWeight state)
    (fun branch sample =>
      P.executionSignature fee hfee C .uncapped accounting
          (P.compiledMenuRule P.certificate.stages P.tools (selectedTable state branch)) sample =
        outcomeSignature P (idealRawRecord P (selectedTable state branch) fee hfee sample).outcome ∧
      runObservationBill (P.input fee hfee) C.val .uncapped accounting
          (P.compiledMenuRule P.certificate.stages P.tools (selectedTable state branch)) sample =
        (idealRawRecord P (selectedTable state branch) fee hfee sample).observation)
    branches
  filter_upwards [allBranches] with sample agreement
  have actions (history : List (VisibleEvent P.sharedInstance)) :
      P.stateRule state sample.1 history =
        P.compiledMenuRule P.certificate.stages P.tools (selectedTable state sample.1.1) sample.1.2 history := by
    rcases sample with ⟨⟨choice, seed⟩, _world⟩
    cases state <;> cases choice <;> rfl
  have runs (clock : ℕ) := searchRun_seed_rule_eq (P.input fee hfee) C.val .uncapped accounting
    (P.stateRule state) (P.compiledMenuRule P.certificate.stages P.tools (selectedTable state sample.1.1))
    sample.1 sample.1.2 actions sample.2 clock
  exact ⟨(executionSignature_eq_of_runs P fee hfee C .uncapped accounting _ _ _ _ runs).trans agreement.1,
    (observationBill_eq_of_runs P fee hfee C .uncapped accounting _ _ _ _ runs).trans agreement.2⟩

/-- Complete execution-signature law for the original generated D25 state.
The actual table invariant, calibration and endpoint finiteness are all
discharged internally. -/
theorem calibratedState_executionSignatureLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (steps : ℕ) :
    let state := P.multiplierSearch fee steps
    P.executionSignatureLaw fee hfee C .uncapped accounting
        (P.calibratedStateRule state) (P.calibratedStateSeedLaw state) =
      P.executionSignatureLaw fee hfee C .uncapped accounting (P.stateRule state) (P.searchSeedLaw state) := by
  dsimp only
  let state := P.multiplierSearch fee steps
  have hc := fun sample => (calibratedState_native_agreement P state fee hfee C accounting sample).1
  have hi := (idealState_native_agreement_ae P state fee hfee C accounting).mono (fun _ h => h.1)
  unfold Parameters.executionSignatureLaw
  calc
    _ = ((P.input fee hfee).seededWorldLaw (P.calibratedStateSeedLaw state)).map
        (fun sample => outcomeSignature P (calibratedSelectedRecord P (selectedTable state) fee hfee sample).outcome) :=
      Measure.map_congr (Filter.Eventually.of_forall hc)
    _ = ((P.input fee hfee).seededWorldLaw (P.searchSeedLaw state)).map
        (fun sample => outcomeSignature P (idealSelectedRecord P (selectedTable state) fee hfee sample).outcome) :=
      calibratedSelectedRecord_signature_law P (selectedTable state)
        (multiplierSearch_selectedTable_levelsValid P fee hfee C accounting steps) (P.stateWeight state) fee hfee
    _ = _ := (Measure.map_congr hi).symm

/-- Original D25 observation comparison, on every original payment contract
and iteration count, with complete failed/nonreturning-path charges. -/
theorem calibratedState_expectedObservationBill_le_four (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (steps : ℕ) :
    let state := P.multiplierSearch fee steps
    expectedObservationBill (P.input fee hfee) C.val .uncapped accounting
        (P.calibratedStateRule state) (P.calibratedStateSeedLaw state) ≤
      4 * expectedObservationBill (P.input fee hfee) C.val .uncapped accounting
        (P.stateRule state) (P.searchSeedLaw state) := by
  dsimp only
  let state := P.multiplierSearch fee steps
  have hc := fun sample => (calibratedState_native_agreement P state fee hfee C accounting sample).2
  have hi := (idealState_native_agreement_ae P state fee hfee C accounting).mono (fun _ h => h.2)
  unfold expectedObservationBill
  calc
    _ = ∫⁻ sample, (calibratedSelectedRecord P (selectedTable state) fee hfee sample).observation
        ∂(P.input fee hfee).seededWorldLaw (P.calibratedStateSeedLaw state) :=
      lintegral_congr_ae (Filter.Eventually.of_forall hc)
    _ ≤ 4 * (∫⁻ sample, (idealSelectedRecord P (selectedTable state) fee hfee sample).observation
        ∂(P.input fee hfee).seededWorldLaw (P.searchSeedLaw state)) :=
      calibratedSelectedRecord_observation_le_four P (selectedTable state)
        (multiplierSearch_selectedTable_levelsValid P fee hfee C accounting steps) (P.stateWeight state) fee hfee
    _ = _ := congrArg (fun value : ℝ≥0∞ => 4 * value) (lintegral_congr_ae hi).symm

end PDROC.CalibratedLaw
