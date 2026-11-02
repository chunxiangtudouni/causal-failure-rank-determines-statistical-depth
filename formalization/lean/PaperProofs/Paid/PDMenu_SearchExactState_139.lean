module

public import PaperProofs.Paid.PDMenu_SearchMixtureRecords_135
public import PaperProofs.Paid.PDMenu_SearchWeakDuality_136
public import PaperProofs.Paid.PDMenu_SearchBracketInvariant_134

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem searchExact_expectedBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance) (solution : MultiplierSolve) :
    expectedBill (P.input fee hfee) C.val mode accounting (P.stateRule (.exact solution)) (P.searchSeedLaw (.exact solution)) =
      expectedBill (P.input fee hfee) C.val mode accounting (P.solveRule solution) (menuSeedLaw P.certificate.stages P.tools) := by
  unfold expectedBill
  rw [searchCoin_integral P fee hfee (.exact solution) _
    (measurable_runActualBill (P.input fee hfee) C.val mode accounting (P.stateRule (.exact solution)) (P.stateRule_measurable _))]
  simp only [PaperProofs.Paid.Parameters.stateWeight, ENNReal.ofReal_zero, sub_zero, ENNReal.ofReal_one,
    zero_mul, one_mul, zero_add]
  apply lintegral_congr
  intro sample
  exact searchBill_seed_rule_eq (P.input fee hfee) C.val mode accounting (P.stateRule (.exact solution)) (P.solveRule solution)
    (false, sample.1) sample.1 (by intro; rfl) sample.2

theorem searchExact_risk (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance) (solution : MultiplierSolve) :
    risk (P.input fee hfee) C.val mode accounting (P.stateRule (.exact solution)) (P.searchSeedLaw (.exact solution)) =
      risk (P.input fee hfee) C.val mode accounting (P.solveRule solution) (menuSeedLaw P.certificate.stages P.tools) := by
  classical
  let input := P.input fee hfee
  let rule := P.stateRule (.exact solution)
  let f := {sample | ¬runSuccess input C.val mode accounting rule sample}.indicator (fun _ => (1 : ℝ≥0∞))
  have hmeas := P.stateRule_measurable (.exact solution)
  have hm : Measurable f := measurable_const.indicator
    (measurableSet_runSuccess input C.val mode accounting rule hmeas).compl
  rw [searchRisk_integral input C.val mode accounting rule hmeas, searchCoin_integral P fee hfee (.exact solution) f hm]
  simp only [PaperProofs.Paid.Parameters.stateWeight, ENNReal.ofReal_zero, sub_zero, ENNReal.ofReal_one,
    zero_mul, one_mul, zero_add]
  rw [searchRisk_integral input C.val mode accounting (P.solveRule solution) (measurable_of_countable _)]
  apply lintegral_congr
  intro sample
  dsimp only [f]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq,
    searchSuccess_seed_rule_eq input C.val mode accounting rule (P.solveRule solution) (false, sample.1) sample.1 (by intro; rfl) sample.2]
  rfl

theorem searchExact_records (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (solution : MultiplierSolve)
    (hstate : P.StateBracketCorrect fee hfee C accounting (.exact solution)) :
    risk (P.input fee hfee) C.val .uncapped accounting (P.stateRule (.exact solution)) (P.searchSeedLaw (.exact solution)) = P.targetRisk ∧
    expectedBill (P.input fee hfee) C.val .uncapped accounting (P.stateRule (.exact solution)) (P.searchSeedLaw (.exact solution)) =
      ENNReal.ofReal (P.solveCost fee solution : ℝ) ∧
    ENNReal.ofReal (P.solveCost fee solution : ℝ) = P.uncappedValue C accounting fee hfee := by
  obtain ⟨hsolve, hm, _, hr⟩ := hstate
  have hris : risk (P.input fee hfee) C.val .uncapped accounting (P.stateRule (.exact solution)) (P.searchSeedLaw (.exact solution)) = P.targetRisk := by
    rw [searchExact_risk P fee hfee C .uncapped accounting solution, hsolve.2.2.1, hr]
    rfl
  have hbill : expectedBill (P.input fee hfee) C.val .uncapped accounting (P.stateRule (.exact solution)) (P.searchSeedLaw (.exact solution)) =
      ENNReal.ofReal (P.solveCost fee solution : ℝ) := by
    rw [searchExact_expectedBill P fee hfee C .uncapped accounting solution, hsolve.2.1]
  have hlower := searchMixtureLower_le_value P fee hfee C accounting solution hsolve hm
  have hrecord : P.mixtureLower fee solution = P.solveCost fee solution := by
    unfold PaperProofs.Paid.Parameters.mixtureLower
    rw [searchRecord_objective, hr]
    ring
  rw [hrecord] at hlower
  have hupper : P.uncappedValue C accounting fee hfee ≤ ENNReal.ofReal (P.solveCost fee solution : ℝ) := by
    have h := value_le_policy (P.input fee hfee) C.val .uncapped accounting P.targetRisk (P.searchSeedLaw (.exact solution))
      (P.statePolicy (.exact solution) fee hfee C accounting) hris.le
    change P.uncappedValue C accounting fee hfee ≤
      expectedBill (P.input fee hfee) C.val .uncapped accounting (P.stateRule (.exact solution))
        (P.searchSeedLaw (.exact solution)) at h
    rw [hbill] at h
    exact h
  exact ⟨hris, hbill, le_antisymm hlower hupper⟩

end PDMenu
