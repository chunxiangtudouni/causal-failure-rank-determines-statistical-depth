module

public import PaperProofs.Common.NativeRun

/-!
The independent normal-fee interface of `model.tex:51-55` and
`price-proofs.tex:302-308`. Normal charges are supplied separately from the
variable ledger. The success lower bound, constructed-run upper bound and
normal-call certificate below are specifications to be supplied for the
original interface/controller; no arbitrary native policy is assumed to
satisfy them. No new legality condition or cross-seed total-value infimum is
introduced.
-/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- A separate actual normal-charge function. Measurability is bookkeeping,
not a fee bound or a controller performance assertion. -/
structure NormalCharges (input : StatisticalInput I) (Seed : Type*) [MeasurableSpace Seed] where
  normalCharge : Seed × input.World → ℝ≥0∞
  measurable_normalCharge : Measurable normalCharge

/-- Original normal-fee assumption: each successful run pays at least C0.
Failed runs retain whatever normal charge the supplied interface assigns. -/
def SuccessfulNormalChargeLower (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (p : Policy input C mode accounting Seed) (normal : NormalCharges input Seed)
    (C0 : ℝ≥0∞) : Prop :=
  ∀ sample, runSuccess input C mode accounting p.rule sample → C0 ≤ normal.normalCharge sample

/-- Controller specification from the manuscript, not a theorem about every policy. -/
def ConstructedNormalChargeUpper (input : StatisticalInput I)
    (normal : NormalCharges input Seed) (C0 : ℝ≥0∞) : Prop :=
  ∀ sample, normal.normalCharge sample ≤ C0

/-- A pathwise normal-call certificate for one selected controller. H0 is not
inserted into native legality and does not bound arbitrary comparison policies. -/
def NormalCallCertificate (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (p : Policy input C mode accounting Seed) (H0 : ℕ) : Prop :=
  ∀ sample n, (run input C mode accounting p.rule sample n).ledger.normalCalls ≤ (H0 : ℕ∞)

noncomputable def expectedNormalCharge (input : StatisticalInput I)
    (normal : NormalCharges input Seed) (ν : Measure Seed) : ℝ≥0∞ :=
  ∫⁻ sample, normal.normalCharge sample ∂input.seededWorldLaw ν

noncomputable def totalRunBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (p : Policy input C mode accounting Seed) (normal : NormalCharges input Seed)
    (sample : Seed × input.World) : ℝ≥0∞ :=
  runActualBill input C mode accounting p.rule sample + normal.normalCharge sample

theorem measurable_totalRunBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (p : Policy input C mode accounting Seed) (normal : NormalCharges input Seed) :
    Measurable (totalRunBill input C mode accounting p normal) :=
  (measurable_runActualBill input C mode accounting p.rule p.measurable_rule).add
    normal.measurable_normalCharge

noncomputable def totalExpectedBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (p : Policy input C mode accounting Seed) (normal : NormalCharges input Seed)
    (ν : Measure Seed) : ℝ≥0∞ :=
  ∫⁻ sample, totalRunBill input C mode accounting p normal sample ∂input.seededWorldLaw ν

/-- Exact all-path additivity, including infinite variable or normal expectations. -/
theorem totalExpectedBill_eq_add (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (p : Policy input C mode accounting Seed) (normal : NormalCharges input Seed)
    (ν : Measure Seed) :
    totalExpectedBill input C mode accounting p normal ν =
      expectedBill input C mode accounting p.rule ν + expectedNormalCharge input normal ν := by
  exact lintegral_add_left
    (measurable_runActualBill input C mode accounting p.rule p.measurable_rule) _

theorem successMeasure_eq_one_sub_risk (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (p : Policy input C mode accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    input.seededWorldLaw ν {sample | runSuccess input C mode accounting p.rule sample} =
      1 - risk input C mode accounting p.rule ν := by
  have hs := measurableSet_runSuccess input C mode accounting p.rule p.measurable_rule
  have h := measure_compl (μ := input.seededWorldLaw ν) hs.compl
    (measure_ne_top _ _)
  simpa only [Set.compl_ofPred, not_not, measure_univ, risk] using h

theorem expectedNormalCharge_lower_of_safe (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (p : Policy input C mode accounting Seed) (normal : NormalCharges input Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (δ C0 : ℝ≥0∞)
    (hsafe : risk input C mode accounting p.rule ν ≤ δ)
    (hcharge : SuccessfulNormalChargeLower input C mode accounting p normal C0) :
    (1 - δ) * C0 ≤ expectedNormalCharge input normal ν := by
  have hs := measurableSet_runSuccess input C mode accounting p.rule p.measurable_rule
  have hsuccess : 1 - δ ≤
      input.seededWorldLaw ν {sample | runSuccess input C mode accounting p.rule sample} := by
    rw [successMeasure_eq_one_sub_risk input C mode accounting p ν]
    exact tsub_le_tsub_left hsafe 1
  calc
    _ ≤ input.seededWorldLaw ν {sample | runSuccess input C mode accounting p.rule sample} * C0 :=
      mul_le_mul' hsuccess le_rfl
    _ = C0 * input.seededWorldLaw ν {sample | runSuccess input C mode accounting p.rule sample} :=
      mul_comm _ _
    _ = ∫⁻ sample, {sample | runSuccess input C mode accounting p.rule sample}.indicator
        (fun _ => C0) sample ∂input.seededWorldLaw ν := (lintegral_indicator_const hs C0).symm
    _ ≤ expectedNormalCharge input normal ν := by
      apply lintegral_mono
      intro sample
      by_cases h : runSuccess input C mode accounting p.rule sample
      · have hmem : sample ∈ {sample | runSuccess input C mode accounting p.rule sample} := h
        rw [Set.indicator_of_mem hmem]
        exact hcharge sample h
      · have hnotmem : sample ∉ {sample | runSuccess input C mode accounting p.rule sample} := h
        rw [Set.indicator_of_notMem hnotmem]
        exact zero_le

theorem expectedNormalCharge_upper_of_constructed (input : StatisticalInput I)
    (normal : NormalCharges input Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (C0 : ℝ≥0∞) (hcharge : ConstructedNormalChargeUpper input normal C0) :
    expectedNormalCharge input normal ν ≤ C0 := by
  have h := lintegral_mono hcharge (μ := input.seededWorldLaw ν)
  simpa only [expectedNormalCharge, lintegral_const, measure_univ, mul_one] using h

theorem totalExpectedBill_lower_of_safe (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (p : Policy input C mode accounting Seed) (normal : NormalCharges input Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (δ C0 : ℝ≥0∞)
    (hsafe : risk input C mode accounting p.rule ν ≤ δ)
    (hcharge : SuccessfulNormalChargeLower input C mode accounting p normal C0) :
    expectedBill input C mode accounting p.rule ν + (1 - δ) * C0 ≤
      totalExpectedBill input C mode accounting p normal ν := by
  rw [totalExpectedBill_eq_add]
  exact add_le_add le_rfl
    (expectedNormalCharge_lower_of_safe input C mode accounting p normal ν δ C0 hsafe hcharge)

theorem totalExpectedBill_upper_of_constructed (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (p : Policy input C mode accounting Seed) (normal : NormalCharges input Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (C0 : ℝ≥0∞)
    (hcharge : ConstructedNormalChargeUpper input normal C0) :
    totalExpectedBill input C mode accounting p normal ν ≤
      expectedBill input C mode accounting p.rule ν + C0 := by
  rw [totalExpectedBill_eq_add]
  exact add_le_add le_rfl (expectedNormalCharge_upper_of_constructed input normal ν C0 hcharge)

end PaperProofs.Common.Native
