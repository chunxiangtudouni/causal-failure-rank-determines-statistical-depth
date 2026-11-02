module

public import PaperProofs.Retained.PRet_FreshTerminalBoundary_040
public import PaperProofs.Retained.PRet_FullMatchingRank_043
public import PaperProofs.Common.ReferenceCostAsymptotics

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshInfiniteBoundary044

open Common Common.Native MeasureTheory
open PRetFreshOldObligation039 PRetFreshTerminalBoundary040 PRetFullMatchingRank043
open scoped ENNReal

variable {I : Instance}

theorem freshSuccess_of_joint_runSuccess {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (hjoint : Matchable I (old ∪ (stagesFrom I next).toFinset))
    (source : PolicyRule (I.freshSuffix next) Seed) (sample : Seed × (input.freshSuffix next).World)
    (hsuccess : runSuccess (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next)) source sample) :
    freshSuccess input next old source sample := by
  obtain ⟨n, hh, hs⟩ := hsuccess
  exact ⟨n, hh, hs.1, hs.2.1,
    hjoint.subset (Finset.union_subset_union (Finset.Subset.refl _)
      (liftedErrors_subset_future I next _))⟩

/-- Reuse a REAL existing zero-observation controller as one admissible
witness. The original joint old-H matching predicate is checked separately;
no retained F = available-tool G identification is made. -/
theorem reference_freshSuccess_of_retained_top {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (htop : errorRank I (stagesFrom I next) old = ⊤)
    (sample : Seed × (input.freshSuffix next).World) :
    freshSuccess input next old
      (referenceRule (input.freshSuffix next) (I.freshSuffix next).tools (1 / 4) none) sample := by
  apply freshSuccess_of_joint_runSuccess input next old
    (top_joint_future_matchable I next old htop)
  exact referenceRun_success_of_infinite_rank (input.freshSuffix next) (freshContract (I.freshSuffix next)) rfl
    (zeroNormalAccounting (I.freshSuffix next)) (I.freshSuffix next).tools (1 / 4)
    (by norm_num) (by norm_num) (fresh_ordered_rank_top_of_retained_top I next old htop) none sample

theorem reference_freshRisk_zero_of_retained_top {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (htop : errorRank I (stagesFrom I next) old = ⊤) (ν : Measure Seed) :
    freshRisk input next old
      (referenceRule (input.freshSuffix next) (I.freshSuffix next).tools (1 / 4) none) ν = 0 := by
  have hset : {sample : Seed × (input.freshSuffix next).World | ¬ freshSuccess input next old
      (referenceRule (input.freshSuffix next) (I.freshSuffix next).tools (1 / 4) none) sample} = ∅ := by
    ext sample
    change (¬ freshSuccess input next old
      (referenceRule (input.freshSuffix next) (I.freshSuffix next).tools (1 / 4) none) sample) ↔ False
    constructor
    · intro hfail
      exact hfail (reference_freshSuccess_of_retained_top input next old htop sample)
    · exact False.elim
  rw [freshRisk, hset, measure_empty]

theorem freshPenalty_zero_of_retained_top (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (htop : errorRank I (stagesFrom I next) old = ⊤) (penalty : ℝ≥0∞) :
    freshPenalty input next old penalty = 0 := by
  have h := freshPenalty_le_policy input next old penalty (Measure.dirac ())
    (referenceUncappedPolicy (input.freshSuffix next) (freshContract (I.freshSuffix next)) rfl
      (zeroNormalAccounting (I.freshSuffix next)) (I.freshSuffix next).tools (1 / 4) none)
  change _ ≤ freshObjective input next old
    (referenceRule (input.freshSuffix next) (I.freshSuffix next).tools (1 / 4) none) (Measure.dirac ()) penalty at h
  rw [freshObjective,
    referenceExpectedObservationBill_infiniteRank (input.freshSuffix next) (freshContract (I.freshSuffix next)) rfl
      (zeroNormalAccounting (I.freshSuffix next)) (I.freshSuffix next).tools (1 / 4) (by norm_num) (by norm_num)
      (fresh_ordered_rank_top_of_retained_top I next old htop) none (Measure.dirac ()),
    reference_freshRisk_zero_of_retained_top input next old htop (Measure.dirac ()),
    mul_zero, add_zero] at h
  exact le_antisymm h bot_le

/-- ALL THREE original fresh boundary clauses, with original old H. The
other original R04 recursion/bridge/asymptotic obligations remain separate. -/
theorem freshPenaltyBoundaryClaims (input : StatisticalInput I) : FreshPenaltyBoundaryClaims input := by
  refine ⟨?_, ?_, ?_⟩
  · intro next old penalty hbad
    exact freshPenalty_unmatchable_old input next old hbad penalty
  · intro next old penalty hnext hmatch
    exact freshPenalty_past_end input next hnext old hmatch penalty
  · intro next old _ htop penalty
    exact freshPenalty_zero_of_retained_top input next old htop penalty

end PaperProofs.Retained.PRetFreshInfiniteBoundary044
