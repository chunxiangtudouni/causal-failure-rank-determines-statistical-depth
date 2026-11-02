module
public import PaperProofs.Paid.PDROC_LocalRecord_009
public import PaperProofs.Common.ReferenceGlobalCost
public import PaperProofs.Common.EntryContinuationPartition

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid

namespace PDROC
universe u

/-- A never-entered stage buys no reviews, including on nonreturn paths. -/
theorem runStageObservationBill_zero_of_no_entry {I : Instance} {Seed : Type u}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (stage : I.Stage) (sample : Seed × input.World)
    (hnone : entryHistory input C mode accounting rule stage sample = none) :
    runStageObservationBill input C mode accounting rule stage sample = 0 := by
  unfold runStageObservationBill
  apply ENNReal.iSup_eq_zero.mpr
  intro n
  have hreview := (run_cursorInvariant input C mode accounting rule hlegal sample n).future_reviews stage
    (run_cursor_lt_of_no_entry input C mode accounting rule hlegal sample stage hnone n)
  rw [hreview]
  simp

/-- The unique first-entry time partitions every actual stage bill without
normalization, double counting, or dropping never-entered failing paths. -/
theorem stageBill_eq_tsum_firstEntry {I : Instance} {Seed : Type u}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (stage : I.Stage) (sample : Seed × input.World) :
    (∑' start : ℕ, {sample | FirstEntryAt input C mode accounting rule stage.val start sample}.indicator
      (runStageObservationBill input C mode accounting rule stage) sample) =
      runStageObservationBill input C mode accounting rule stage sample := by
  classical
  by_cases hex : ∃ start, FirstEntryAt input C mode accounting rule stage.val start sample
  · obtain ⟨start, hstart⟩ := hex
    rw [tsum_eq_single start]
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hstart, ↓reduceIte]
    · intro other hother
      have hne : ¬ FirstEntryAt input C mode accounting rule stage.val other sample := by
        intro ho
        exact hother (EntryContinuationPartition.firstEntry_unique input C mode accounting rule stage sample other start ho hstart)
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, hne, ↓reduceIte]
  · have hnone : entryHistory input C mode accounting rule stage sample = none := by
      apply (entryHistory_none_iff input C mode accounting rule stage sample).mpr
      intro hcursor
      apply hex
      exact ⟨Nat.find hcursor, Nat.find_spec hcursor, fun k hk => Nat.find_min hcursor hk⟩
    have hzero := runStageObservationBill_zero_of_no_entry input C mode accounting rule hlegal stage sample hnone
    rw [hzero]
    apply ENNReal.tsum_eq_zero.mpr
    intro start
    have hne : ¬ FirstEntryAt input C mode accounting rule stage.val start sample := fun h => hex ⟨start, h⟩
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hne, ↓reduceIte]

section
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Exact expected stage bill as the sum of its true first-entry atoms.
ENNReal Tonelli handles infinite expected bills with no extra premise. -/
theorem expectedStageBill_eq_tsum_firstEntry {I : Instance}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (source : Policy input C mode accounting Seed)
    (ν : Measure Seed) (stage : I.Stage) :
    (∑' start : ℕ, ∫⁻ sample, {sample | FirstEntryAt input C mode accounting source.rule stage.val start sample}.indicator
      (runStageObservationBill input C mode accounting source.rule stage) sample ∂input.seededWorldLaw ν) =
      ∫⁻ sample, runStageObservationBill input C mode accounting source.rule stage sample ∂input.seededWorldLaw ν := by
  have hm (start : ℕ) : AEMeasurable
      ({sample | FirstEntryAt input C mode accounting source.rule stage.val start sample}.indicator
        (runStageObservationBill input C mode accounting source.rule stage)) (input.seededWorldLaw ν) :=
    ((measurable_runStageObservationBill input C mode accounting source.rule source.measurable_rule stage).indicator
      (measurableSet_firstEntryAt input C mode accounting source.rule source.measurable_rule stage.val start)).aemeasurable
  rw [← lintegral_tsum hm]
  apply lintegral_congr
  intro sample
  exact stageBill_eq_tsum_firstEntry input C mode accounting source.rule source.legal stage sample

/-- The local source kernels account for each actual original observation
exactly once, stage by stage and first-entry clock by first-entry clock.
No finite-bill, success, MAP, or Markov restriction is imposed. -/
theorem sourceObservationBill_eq_sum_localCharges (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∑ first : P.sharedInstance.Stage, ∑' start : ℕ,
      P.binarySymmetric.experiment.bayesObservationCharge
        (sourceEntrySeedLaw P fee hfee C mode accounting source ν first start)
        (optionalSourceEntryTest P fee hfee first accounting source.rule source.measurable_rule)) =
      expectedObservationBill (P.input fee hfee) C.val mode accounting source.rule ν := by
  simp_rw [optionalSourceEntryTest_bayesCharge_eq_entryStageBill]
  rw [expectedObservationBill_eq_sum_stage (P.input fee hfee) C.val mode accounting source.rule source.legal source.measurable_rule ν]
  apply Finset.sum_congr rfl
  intro stage _
  exact expectedStageBill_eq_tsum_firstEntry (P.input fee hfee) C.val mode accounting source ν stage

end
end PDROC


