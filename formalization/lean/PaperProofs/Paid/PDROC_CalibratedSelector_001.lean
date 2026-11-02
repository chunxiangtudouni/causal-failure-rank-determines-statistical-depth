module

public import PaperProofs.Paid.CalibratedBackend
public import PaperProofs.Common.AvailableValue

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid MeasureTheory
open scoped ENNReal

namespace PDROC.CalibratedSelector

variable {I : Instance}

theorem runSuccess_seed_projection {Large Small : Type*} [MeasurableSpace Large] [MeasurableSpace Small]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Large) (target : PolicyRule I Small) (project : Large → Small)
    (same : ∀ seed history, rule seed history = target (project seed) history)
    (sample : Large × input.World) :
    runSuccess input C mode accounting rule sample ↔
      runSuccess input C mode accounting target (project sample.1, sample.2) := by
  have runs (n : ℕ) : run input C mode accounting rule sample n =
      run input C mode accounting target (project sample.1, sample.2) n :=
    searchRun_seed_rule_eq input C mode accounting rule target sample.1 (project sample.1)
      (same sample.1) sample.2 n
  simp only [runSuccess, runs]

theorem risk_seed_projection {Large Small : Type*} [MeasurableSpace Large] [MeasurableSpace Small]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Large) (target : PolicyRule I Small) (project : Large → Small)
    (measurable : Measurable project) (target_measurable : MeasurableRule target)
    (same : ∀ seed history, rule seed history = target (project seed) history) (ν : Measure Large) :
    risk input C mode accounting rule ν = risk input C mode accounting target (ν.map project) := by
  symm
  unfold risk
  have joint_measurable : Measurable (fun sample : Large × input.World => (project sample.1, sample.2)) :=
    (measurable.comp measurable_fst).prodMk measurable_snd
  have failure_measurable : MeasurableSet {sample : Small × input.World |
      ¬ runSuccess input C mode accounting target sample} :=
    (measurableSet_runSuccess input C mode accounting target target_measurable).compl
  rw [seededWorldLaw_map_seed input ν project measurable, Measure.map_apply joint_measurable failure_measurable]
  congr 1
  ext sample
  exact (not_congr (runSuccess_seed_projection input C mode accounting rule target project same sample)).symm

theorem expectedBill_seed_projection {Large Small : Type*} [MeasurableSpace Large] [MeasurableSpace Small]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Large) (target : PolicyRule I Small) (project : Large → Small)
    (measurable : Measurable project) (target_measurable : MeasurableRule target)
    (same : ∀ seed history, rule seed history = target (project seed) history) (ν : Measure Large) :
    expectedBill input C mode accounting rule ν =
      expectedBill input C mode accounting target (ν.map project) := by
  symm
  unfold expectedBill
  have joint_measurable : Measurable (fun sample : Large × input.World => (project sample.1, sample.2)) :=
    (measurable.comp measurable_fst).prodMk measurable_snd
  rw [seededWorldLaw_map_seed input ν project measurable,
    lintegral_map (measurable_runActualBill input C mode accounting target target_measurable) joint_measurable]
  apply lintegral_congr
  intro sample
  exact (searchBill_seed_rule_eq input C mode accounting rule target sample.1 (project sample.1)
    (same sample.1) sample.2).symm

def projectSearchSeed (P : Parameters) (seed : P.CalibratedSearchSeed) : P.SearchSeed :=
  (seed.1, seed.2.1)

theorem measurable_projectSearchSeed (P : Parameters) : Measurable (projectSearchSeed P) :=
  measurable_fst.prodMk (measurable_fst.comp measurable_snd)

theorem zeroBranch_rule_eq_zeroCharge (P : Parameters) (fee : ℚ)
    (zeroBranch : P.zeroChargeRisk fee ≤ P.certificate.risk)
    (seed : P.CalibratedSearchSeed) (history : List (VisibleEvent P.sharedInstance)) :
    P.calibratedAlgorithmRule fee seed history = P.zeroChargeRule fee seed.2.1 history := by
  unfold Parameters.calibratedAlgorithmRule Parameters.calibratedAlgorithmCandidate
  rw [ite_eq_left zeroBranch]
  rfl

theorem zeroBranch_rule_eq_ideal (P : Parameters) (fee : ℚ)
    (zeroBranch : P.zeroChargeRisk fee ≤ P.certificate.risk)
    (seed : P.CalibratedSearchSeed) (history : List (VisibleEvent P.sharedInstance)) :
    P.calibratedAlgorithmRule fee seed history = P.idealSearchRule fee (projectSearchSeed P seed) history := by
  unfold Parameters.idealSearchRule
  rw [ite_eq_left zeroBranch]
  exact zeroBranch_rule_eq_zeroCharge P fee zeroBranch seed history

theorem zeroBranch_seedLaw_eq_ideal (P : Parameters) (fee : ℚ)
    (zeroBranch : P.zeroChargeRisk fee ≤ P.certificate.risk) :
    (P.calibratedAlgorithmSeedLaw fee).map (projectSearchSeed P) = P.idealSearchSeedLaw fee := by
  simp only [Parameters.calibratedAlgorithmSeedLaw, Parameters.idealSearchSeedLaw, ite_eq_left zeroBranch]
  change (((Measure.dirac false).prod P.calibratedMenuSeedLaw).map
    (Prod.map (id : Bool → Bool) (Prod.fst : P.CalibratedMenuSeed → MenuSeed P.certificate.stages P.tools))) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_fst]
  simp only [Measure.map_id, Parameters.calibratedMenuSeedLaw, Measure.map_fst_prod, measure_univ, one_smul]

theorem zeroBranch_run_eq_ideal (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (zeroBranch : P.zeroChargeRisk fee ≤ P.certificate.risk)
    (sample : P.CalibratedSearchSeed × (P.input fee hfee).World) (n : ℕ) :
    run (P.input fee hfee) C.val mode accounting (P.calibratedAlgorithmRule fee) sample n =
      run (P.input fee hfee) C.val mode accounting (P.idealSearchRule fee)
        (projectSearchSeed P sample.1, sample.2) n :=
  searchRun_seed_rule_eq (P.input fee hfee) C.val mode accounting (P.calibratedAlgorithmRule fee)
    (P.idealSearchRule fee) sample.1 (projectSearchSeed P sample.1)
    (zeroBranch_rule_eq_ideal P fee zeroBranch sample.1) sample.2 n

theorem zeroBranch_risk_eq_ideal (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (zeroBranch : P.zeroChargeRisk fee ≤ P.certificate.risk) :
    risk (P.input fee hfee) C.val mode accounting (P.calibratedAlgorithmRule fee) (P.calibratedAlgorithmSeedLaw fee) =
      risk (P.input fee hfee) C.val mode accounting (P.idealSearchRule fee) (P.idealSearchSeedLaw fee) := by
  rw [risk_seed_projection (P.input fee hfee) C.val mode accounting (P.calibratedAlgorithmRule fee)
    (P.idealSearchRule fee) (projectSearchSeed P) (measurable_projectSearchSeed P)
    (measurable_of_countable _) (zeroBranch_rule_eq_ideal P fee zeroBranch)]
  rw [zeroBranch_seedLaw_eq_ideal P fee zeroBranch]

theorem zeroBranch_expectedBill_eq_ideal (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (zeroBranch : P.zeroChargeRisk fee ≤ P.certificate.risk) :
    expectedBill (P.input fee hfee) C.val mode accounting (P.calibratedAlgorithmRule fee)
      (P.calibratedAlgorithmSeedLaw fee) =
        expectedBill (P.input fee hfee) C.val mode accounting (P.idealSearchRule fee) (P.idealSearchSeedLaw fee) := by
  rw [expectedBill_seed_projection (P.input fee hfee) C.val mode accounting (P.calibratedAlgorithmRule fee)
    (P.idealSearchRule fee) (projectSearchSeed P) (measurable_projectSearchSeed P)
    (measurable_of_countable _) (zeroBranch_rule_eq_ideal P fee zeroBranch)]
  rw [zeroBranch_seedLaw_eq_ideal P fee zeroBranch]

end PDROC.CalibratedSelector
