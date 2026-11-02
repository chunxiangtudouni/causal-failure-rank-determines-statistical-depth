module

public import PaperProofs.Paid.PDMenu_ZeroChargeActualRisk_147
public import PaperProofs.Paid.PDMenu_ZeroChargeBill_145
public import PaperProofs.Paid.PDMenu_SearchMixtureRecords_135

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem searchLift_risk (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance (MenuSeed P.certificate.stages P.tools)) (hmeas : MeasurableRule rule) :
    risk (P.input fee hfee) C.val mode accounting (fun seed : P.SearchSeed => rule seed.2)
      ((Measure.dirac false).prod (menuSeedLaw P.certificate.stages P.tools)) =
      risk (P.input fee hfee) C.val mode accounting rule (menuSeedLaw P.certificate.stages P.tools) := by
  classical
  let lifted : PolicyRule P.sharedInstance P.SearchSeed := fun seed => rule seed.2
  have hml : MeasurableRule lifted := hmeas.comp (measurable_fst.snd.prodMk measurable_snd)
  let state := MultiplierState.exact (P.solveMultiplier fee 0)
  have hlaw : P.searchSeedLaw state = (Measure.dirac false).prod (menuSeedLaw P.certificate.stages P.tools) := by
    simp only [PaperProofs.Paid.Parameters.searchSeedLaw, state, PaperProofs.Paid.Parameters.stateWeight,
      PaperProofs.Statistics.BinarySymmetric.Parameters.rocCoinLaw, ENNReal.ofReal_zero, zero_smul,
      sub_zero, ENNReal.ofReal_one, one_smul, zero_add]
  let input := P.input fee hfee
  let f := {sample | ¬runSuccess input C.val mode accounting lifted sample}.indicator (fun _ => (1:ℝ≥0∞))
  have hf : Measurable f := measurable_const.indicator (measurableSet_runSuccess input C.val mode accounting lifted hml).compl
  rw [searchRisk_integral input C.val mode accounting lifted hml, ← hlaw, searchCoin_integral P fee hfee state f hf]
  simp only [state, PaperProofs.Paid.Parameters.stateWeight, ENNReal.ofReal_zero, zero_mul, sub_zero,
    ENNReal.ofReal_one, one_mul, zero_add]
  rw [searchRisk_integral input C.val mode accounting rule hmeas]
  apply lintegral_congr
  intro sample
  dsimp only [f]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq,
    searchSuccess_seed_rule_eq input C.val mode accounting lifted rule (false,sample.1) sample.1 (by intro; rfl) sample.2]
  rfl

theorem idealSearch_zero_records (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (hzero : P.zeroChargeRisk fee ≤ P.certificate.risk) :
    expectedBill (P.input fee hfee) C.val .uncapped accounting (P.idealSearchRule fee) (P.idealSearchSeedLaw fee) = 0 ∧
      risk (P.input fee hfee) C.val .uncapped accounting (P.idealSearchRule fee) (P.idealSearchSeedLaw fee) ≤ P.targetRisk := by
  have hbill : ∀ sample : P.SearchSeed × (P.input fee hfee).World,
      runActualBill (P.input fee hfee) C.val .uncapped accounting
        (fun seed : P.SearchSeed => P.zeroChargeRule fee seed.2) sample = 0 := by
    intro sample
    have h := searchBill_seed_rule_eq (P.input fee hfee) C.val .uncapped accounting
      (fun seed : P.SearchSeed => P.zeroChargeRule fee seed.2) (P.zeroChargeRule fee) sample.1 sample.1.2
      (by intro; rfl) sample.2
    exact h.trans (zeroCharge_runActualBill P fee hfee C accounting (sample.1.2,sample.2))
  rw [PaperProofs.Paid.Parameters.idealSearchRule, PaperProofs.Paid.Parameters.idealSearchSeedLaw,
    ite_eq_left hzero, ite_eq_left hzero]
  constructor
  · simp only [expectedBill, hbill, lintegral_zero]
  · rw [searchLift_risk P fee hfee C .uncapped accounting (P.zeroChargeRule fee) (measurable_of_countable _),
      zeroCharge_risk P fee hfee C accounting]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hzero)

end PDMenu
