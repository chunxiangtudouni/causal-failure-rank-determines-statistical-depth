module

public import PaperProofs.Retained.PRet_FreshExtractionPolicy_047

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshCharge065

open Common Common.Native MeasureTheory
open scoped ENNReal

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def freshCharge (input : StatisticalInput I) (first : ℕ) (old : Finset I.Stage)
    (rule : PolicyRule (I.freshSuffix first) Seed) (penalty : ℝ≥0∞)
    (sample : Seed × (input.freshSuffix first).World) : ℝ≥0∞ := by
  classical
  exact runObservationBill (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) rule sample +
      if freshSuccess input first old rule sample then 0 else penalty

theorem measurable_freshCharge (input : StatisticalInput I) (first : ℕ) (old : Finset I.Stage)
    (rule : PolicyRule (I.freshSuffix first) Seed) (hm : MeasurableRule rule) (penalty : ℝ≥0∞) :
    Measurable (freshCharge input first old rule penalty) := by
  classical
  unfold freshCharge
  exact (measurable_runObservationBill _ _ _ _ _ hm).add
    (Measurable.ite (measurableSet_freshSuccess input first old rule hm) measurable_const measurable_const)

theorem freshObjective_eq_lintegral (input : StatisticalInput I) (first : ℕ) (old : Finset I.Stage)
    (rule : PolicyRule (I.freshSuffix first) Seed) (hm : MeasurableRule rule)
    (ν : Measure Seed) (penalty : ℝ≥0∞) :
    freshObjective input first old rule ν penalty =
      ∫⁻ sample, freshCharge input first old rule penalty sample ∂(input.freshSuffix first).seededWorldLaw ν := by
  classical
  have hfail : MeasurableSet {sample | ¬ freshSuccess input first old rule sample} :=
    (measurableSet_freshSuccess input first old rule hm).compl
  have heq : (fun sample => freshCharge input first old rule penalty sample) =
      fun sample => runObservationBill (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first)) rule sample +
          {sample | ¬ freshSuccess input first old rule sample}.indicator (fun _ => penalty) sample := by
    funext sample
    by_cases hs : freshSuccess input first old rule sample <;>
      simp only [freshCharge, hs, ↓reduceIte, Set.indicator, Set.mem_ofPred_eq, not_true_eq_false,
        not_false_eq_true, add_zero]
  rw [heq, lintegral_add_left (measurable_runObservationBill _ _ _ _ _ hm),
    lintegral_indicator_const hfail]
  rfl

/-- Pointwise arbitrary-seed value comparison for the ACTUAL admissible
extracted Policy. Dirac comparison avoids all conditioning/normalization. -/
theorem freshPenalty_le_extraction_dirac (input : StatisticalInput I) (first : ℕ) (old : Finset I.Stage)
    (accounting : NormalAccounting I) (source : PolicyRule I Seed) (hm : MeasurableRule source)
    (startup : Startup I) (seed : Seed) (penalty : ℝ≥0∞) :
    freshPenalty input first old penalty ≤
      ∫⁻ fresh, freshCharge input first old (PRetFreshExtractionPolicy047.rule first accounting source startup)
        penalty (seed, fresh) ∂(input.freshSuffix first).worldLaw := by
  let targetPolicy := PRetFreshExtractionPolicy047.policy input first accounting source hm startup
  have hbound := freshPenalty_le_policy_any_seed input first old penalty (Measure.dirac seed) targetPolicy
  rw [freshObjective_eq_lintegral input first old targetPolicy.rule targetPolicy.measurable_rule] at hbound
  rw [StatisticalInput.seededWorldLaw, Measure.dirac_prod,
    lintegral_map (measurable_freshCharge input first old targetPolicy.rule targetPolicy.measurable_rule penalty)
      measurable_prodMk_left] at hbound
  exact hbound

end PaperProofs.Retained.PRetFreshCharge065


