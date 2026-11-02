module

public import PaperProofs.Paid.PDMenu_SearchCoinIntegral_133

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem searchSuccess_seed_rule_eq {I : Instance} {Seed Seed' : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Seed'] (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (rule' : PolicyRule I Seed')
    (seed : Seed) (seed' : Seed') (heq : ∀ history, rule seed history = rule' seed' history) (world : input.World) :
    runSuccess input C mode accounting rule (seed, world) ↔ runSuccess input C mode accounting rule' (seed', world) := by
  unfold runSuccess
  apply exists_congr
  intro clock
  rw [searchRun_seed_rule_eq input C mode accounting rule rule' seed seed' heq world clock]

theorem searchRisk_integral {I : Instance} {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hmeas : MeasurableRule rule) (ν : Measure Seed) :
    risk input C mode accounting rule ν =
      ∫⁻ sample, {sample | ¬runSuccess input C mode accounting rule sample}.indicator
        (fun _ => (1 : ℝ≥0∞)) sample ∂input.seededWorldLaw ν :=
  (lintegral_indicator_one (μ := input.seededWorldLaw ν) (measurableSet_runSuccess input C mode accounting rule hmeas).compl).symm

theorem searchBracket_expectedBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (lower upper : MultiplierSolve) :
    expectedBill (P.input fee hfee) C.val mode accounting (P.stateRule (.bracket lower upper)) (P.searchSeedLaw (.bracket lower upper)) =
      ENNReal.ofReal (P.clippedMixtureWeight lower upper).val *
        expectedBill (P.input fee hfee) C.val mode accounting (P.solveRule lower) (menuSeedLaw P.certificate.stages P.tools) +
      ENNReal.ofReal (1 - (P.clippedMixtureWeight lower upper).val) *
        expectedBill (P.input fee hfee) C.val mode accounting (P.solveRule upper) (menuSeedLaw P.certificate.stages P.tools) := by
  unfold expectedBill
  rw [searchCoin_integral P fee hfee (.bracket lower upper) _
    (measurable_runActualBill (P.input fee hfee) C.val mode accounting (P.stateRule (.bracket lower upper)) (P.stateRule_measurable _))]
  have ht : (fun sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World =>
      runActualBill (P.input fee hfee) C.val mode accounting (P.stateRule (.bracket lower upper)) ((true, sample.1), sample.2)) =
      (fun sample => runActualBill (P.input fee hfee) C.val mode accounting (P.solveRule lower) sample) := by
    funext sample
    exact P.stateRule_bracket_bill lower upper fee hfee C mode accounting true sample.1 sample.2
  have hf : (fun sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World =>
      runActualBill (P.input fee hfee) C.val mode accounting (P.stateRule (.bracket lower upper)) ((false, sample.1), sample.2)) =
      (fun sample => runActualBill (P.input fee hfee) C.val mode accounting (P.solveRule upper) sample) := by
    funext sample
    exact P.stateRule_bracket_bill lower upper fee hfee C mode accounting false sample.1 sample.2
  rw [ht, hf]
  rfl

theorem searchBracket_risk (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (lower upper : MultiplierSolve) :
    risk (P.input fee hfee) C.val mode accounting (P.stateRule (.bracket lower upper)) (P.searchSeedLaw (.bracket lower upper)) =
      ENNReal.ofReal (P.clippedMixtureWeight lower upper).val *
        risk (P.input fee hfee) C.val mode accounting (P.solveRule lower) (menuSeedLaw P.certificate.stages P.tools) +
      ENNReal.ofReal (1 - (P.clippedMixtureWeight lower upper).val) *
        risk (P.input fee hfee) C.val mode accounting (P.solveRule upper) (menuSeedLaw P.certificate.stages P.tools) := by
  classical
  let input := P.input fee hfee
  let rule := P.stateRule (.bracket lower upper)
  let ν := menuSeedLaw P.certificate.stages P.tools
  let f := {sample | ¬runSuccess input C.val mode accounting rule sample}.indicator (fun _ => (1 : ℝ≥0∞))
  have hmeas := P.stateRule_measurable (.bracket lower upper)
  have hfailure : MeasurableSet {sample | ¬runSuccess input C.val mode accounting rule sample} :=
    (measurableSet_runSuccess input C.val mode accounting rule hmeas).compl
  have hm : Measurable f := measurable_const.indicator hfailure
  have ht : (∫⁻ sample, f ((true, sample.1), sample.2) ∂input.seededWorldLaw ν) =
      risk input C.val mode accounting (P.solveRule lower) ν := by
    rw [searchRisk_integral input C.val mode accounting (P.solveRule lower) (measurable_of_countable _) ν]
    apply lintegral_congr
    intro sample
    dsimp only [f]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    simp only [searchSuccess_seed_rule_eq input C.val mode accounting rule (P.solveRule lower) (true, sample.1) sample.1 (by intro; rfl) sample.2]
  have hf : (∫⁻ sample, f ((false, sample.1), sample.2) ∂input.seededWorldLaw ν) =
      risk input C.val mode accounting (P.solveRule upper) ν := by
    rw [searchRisk_integral input C.val mode accounting (P.solveRule upper) (measurable_of_countable _) ν]
    apply lintegral_congr
    intro sample
    dsimp only [f]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    simp only [searchSuccess_seed_rule_eq input C.val mode accounting rule (P.solveRule upper) (false, sample.1) sample.1 (by intro; rfl) sample.2]
  rw [searchRisk_integral input C.val mode accounting rule hmeas, searchCoin_integral P fee hfee (.bracket lower upper) f hm,
    ht, hf]
  rfl

end PDMenu
