module

public import PaperProofs.Retained.Controller

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshOldObligation039

open Common Common.Native MeasureTheory
open scoped ENNReal

variable {I : Instance}

/-- The original retained fresh success predicate really retains old H. -/
theorem freshSuccess_old_matchable {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (source : PolicyRule (I.freshSuffix next) Seed)
    (sample : Seed × (input.freshSuffix next).World)
    (hs : freshSuccess input next old source sample) : Matchable I old := by
  obtain ⟨n, _, _, _, hmatch⟩ := hs
  exact hmatch.subset Finset.subset_union_left

theorem freshRisk_unmatchable_old {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage) (hbad : ¬ Matchable I old)
    (source : PolicyRule (I.freshSuffix next) Seed) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    freshRisk input next old source ν = 1 := by
  have hset : {sample | ¬ freshSuccess input next old source sample} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro sample hs
    exact hbad (freshSuccess_old_matchable input next old source sample hs)
  simp only [freshRisk, hset, measure_univ]

theorem penalty_le_freshObjective_unmatchable_old {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage) (hbad : ¬ Matchable I old)
    (source : PolicyRule (I.freshSuffix next) Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (penalty : ℝ≥0∞) : penalty ≤ freshObjective input next old source ν penalty := by
  rw [freshObjective, freshRisk_unmatchable_old input next old hbad source ν, mul_one]
  calc
    penalty ≤ penalty + expectedObservationBill (input.freshSuffix next) (freshContract (I.freshSuffix next))
        .uncapped (zeroNormalAccounting (I.freshSuffix next)) source ν := le_self_add
    _ = _ := add_comm _ _

/-- First ORIGINAL R04 fresh-penalty boundary, for all old H and all ENNReal
penalties. No available-tool G, optimal-policy attainment or termination
restriction is substituted for the independently defined full Policy infimum. -/
theorem freshPenalty_unmatchable_old (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (hbad : ¬ Matchable I old) (penalty : ℝ≥0∞) : freshPenalty input next old penalty = penalty := by
  apply le_antisymm (freshPenalty_le_penalty input next old penalty)
  unfold freshPenalty
  apply le_iInf
  intro Seed
  apply le_iInf
  intro m
  let : MeasurableSpace Seed := m
  apply le_iInf
  intro ν
  apply le_iInf
  intro hν
  let : IsProbabilityMeasure ν := hν
  apply le_iInf
  intro source
  exact penalty_le_freshObjective_unmatchable_old input next old hbad source.rule ν penalty

end PaperProofs.Retained.PRetFreshOldObligation039
