module

public import PaperProofs.Retained.PRet_NestedComparison_074

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetJointCharges075

open Common Common.Native MeasureTheory PRetAmbientComparator073 PRetNestedComparison074
open scoped ENNReal

variable {Physical Ambient : Instance} {Seed : Type*}

theorem measurableSet_jointSuccess [MeasurableSpace Seed] (input : StatisticalInput Physical) (embed : Physical.Stage → Ambient.Stage)
    (old : Finset Ambient.Stage) (rule : PolicyRule Physical Seed) (hm : MeasurableRule rule) :
    MeasurableSet {sample | jointSuccess input embed old rule sample} := by
  have hset (n : ℕ) : MeasurableSet {sample : Seed × input.World |
      let state := run input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) rule sample n
      state.halted = true ∧ state.ledger.finished = true ∧ state.ledger.abandoned = false ∧
        Matchable Ambient (old ∪ (ordinaryMismatches state.ledger).image embed)} :=
    (measurable_run input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) rule hm n)
      (MeasurableSpace.measurableSet_top (s := {state : State Physical |
        state.halted = true ∧ state.ledger.finished = true ∧ state.ledger.abandoned = false ∧
          Matchable Ambient (old ∪ (ordinaryMismatches state.ledger).image embed)}))
  have heq : {sample | jointSuccess input embed old rule sample} =
      ⋃ n : ℕ, {sample : Seed × input.World |
        let state := run input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) rule sample n
        state.halted = true ∧ state.ledger.finished = true ∧ state.ledger.abandoned = false ∧
          Matchable Ambient (old ∪ (ordinaryMismatches state.ledger).image embed)} := by
    ext sample
    simp only [jointSuccess, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion hset

noncomputable def jointCharge (input : StatisticalInput Physical) (embed : Physical.Stage → Ambient.Stage)
    (old : Finset Ambient.Stage) (rule : PolicyRule Physical Seed) (penalty : ℝ≥0∞)
    (sample : Seed × input.World) : ℝ≥0∞ := by
  classical
  exact runObservationBill input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) rule sample +
    if jointSuccess input embed old rule sample then 0 else penalty

theorem measurable_jointCharge [MeasurableSpace Seed] (input : StatisticalInput Physical) (embed : Physical.Stage → Ambient.Stage)
    (old : Finset Ambient.Stage) (rule : PolicyRule Physical Seed) (hm : MeasurableRule rule) (penalty : ℝ≥0∞) :
    Measurable (jointCharge input embed old rule penalty) := by
  classical
  exact (measurable_runObservationBill _ _ _ _ _ hm).add
    (Measurable.ite (measurableSet_jointSuccess input embed old rule hm) measurable_const measurable_const)

theorem jointObjective_eq_lintegral [MeasurableSpace Seed] (input : StatisticalInput Physical) (embed : Physical.Stage → Ambient.Stage)
    (old : Finset Ambient.Stage) (rule : PolicyRule Physical Seed) (hm : MeasurableRule rule)
    (ν : Measure Seed) (penalty : ℝ≥0∞) :
    jointObjective input embed old rule ν penalty = ∫⁻ sample, jointCharge input embed old rule penalty sample ∂input.seededWorldLaw ν := by
  classical
  have hfail : MeasurableSet {sample | ¬ jointSuccess input embed old rule sample} :=
    (measurableSet_jointSuccess input embed old rule hm).compl
  have heq : (fun sample => jointCharge input embed old rule penalty sample) =
      fun sample => runObservationBill input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) rule sample +
        {sample | ¬ jointSuccess input embed old rule sample}.indicator (fun _ => penalty) sample := by
    funext sample
    by_cases hs : jointSuccess input embed old rule sample <;>
      simp only [jointCharge, hs, ↓reduceIte, Set.indicator, Set.mem_ofPred_eq, not_true_eq_false,
        not_false_eq_true, add_zero]
  rw [heq, lintegral_add_left (measurable_runObservationBill _ _ _ _ _ hm), lintegral_indicator_const hfail]
  rfl

theorem freshPenalty_le_nested_extraction_dirac [MeasurableSpace Seed] {I : Instance} (input : StatisticalInput I) (first next : ℕ)
    (old : Finset I.Stage) (accounting : NormalAccounting (I.freshSuffix first))
    (source : PolicyRule (I.freshSuffix first) Seed) (hm : MeasurableRule source)
    (startup : Startup (I.freshSuffix first)) (seed : Seed) (penalty : ℝ≥0∞) :
    freshPenalty input (first + next) old penalty ≤
      ∫⁻ world, jointCharge ((input.freshSuffix first).freshSuffix next)
        (fun stage => I.freshStageLift first ((I.freshSuffix first).freshStageLift next stage)) old
        (PRetFreshExtractionPolicy047.rule next accounting source startup) penalty (seed, world)
          ∂((input.freshSuffix first).freshSuffix next).worldLaw := by
  have h := freshPenalty_le_nested_extraction input first next old accounting source hm startup (Measure.dirac seed) penalty
  rw [jointObjective_eq_lintegral _ _ _ _ (PRetFreshExtractionPolicy047.measurable_rule next accounting source hm startup)] at h
  rw [StatisticalInput.seededWorldLaw, Measure.dirac_prod,
    lintegral_map (measurable_jointCharge _ _ _ _ (PRetFreshExtractionPolicy047.measurable_rule next accounting source hm startup) penalty)
      measurable_prodMk_left] at h
  exact h

end PaperProofs.Retained.PRetJointCharges075

