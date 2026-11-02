module

public import PaperProofs.Retained.PRet_FreshOldObligation_039

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshOldMonotonicity041

open Common Common.Native MeasureTheory
open scoped ENNReal

variable {I : Instance}

theorem freshSuccess_of_old_subset {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (next : ℕ) (small large : Finset I.Stage) (hsub : small ⊆ large)
    (source : PolicyRule (I.freshSuffix next) Seed) (sample : Seed × (input.freshSuffix next).World)
    (hs : freshSuccess input next large source sample) : freshSuccess input next small source sample := by
  obtain ⟨n, hh, hf, ha, hm⟩ := hs
  exact ⟨n, hh, hf, ha, hm.subset (Finset.union_subset_union hsub (Finset.Subset.refl _))⟩

theorem freshRisk_mono_old {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (next : ℕ) (small large : Finset I.Stage) (hsub : small ⊆ large)
    (source : PolicyRule (I.freshSuffix next) Seed) (ν : Measure Seed) :
    freshRisk input next small source ν ≤ freshRisk input next large source ν := by
  apply measure_mono
  intro sample hfail hs
  exact hfail (freshSuccess_of_old_subset input next small large hsub source sample hs)

theorem freshObjective_mono_old {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (next : ℕ) (small large : Finset I.Stage) (hsub : small ⊆ large)
    (source : PolicyRule (I.freshSuffix next) Seed) (ν : Measure Seed) (penalty : ℝ≥0∞) :
    freshObjective input next small source ν penalty ≤ freshObjective input next large source ν penalty := by
  unfold freshObjective
  apply add_le_add le_rfl
  have hm := mul_le_mul_right (freshRisk_mono_old input next small large hsub source ν) penalty
  simpa only [mul_comm] using hm

/-- Full retained old-H monotonicity of the independently defined Policy
infimum. No fixed matching, available-tool suffix value, attained optimum,
finite expected bill or successful-path policy restriction is used. -/
theorem freshPenalty_mono_old (input : StatisticalInput I) (next : ℕ)
    (small large : Finset I.Stage) (hsub : small ⊆ large) (penalty : ℝ≥0∞) :
    freshPenalty input next small penalty ≤ freshPenalty input next large penalty := by
  unfold freshPenalty
  apply iInf_mono
  intro Seed
  apply iInf_mono
  intro m
  let : MeasurableSpace Seed := m
  apply iInf_mono
  intro ν
  apply iInf_mono
  intro hν
  let : IsProbabilityMeasure ν := hν
  apply iInf_mono
  intro source
  exact freshObjective_mono_old input next small large hsub source.rule ν penalty

end PaperProofs.Retained.PRetFreshOldMonotonicity041
