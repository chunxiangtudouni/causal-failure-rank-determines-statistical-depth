module

public import PaperProofs.Retained.PRet_RiskMassFlow_Target_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory

namespace PRetRiskMassFlow

variable {I : Instance}

theorem rankCase_noTool_iff (stage : I.Stage) (old : Finset I.Stage) (healthy : Healthy I stage.val old) :
    rankCase I stage old = some .noTool ↔ ¬Matchable I (insert stage old) := by
  classical
  constructor
  · intro noTool
    obtain ⟨kind,query,obstruction⟩ := PRetAlignment.rankCase_exists stage old healthy
    exact obstruction (Option.some.inj (query.symm.trans noTool))
  · intro obstructed
    have badZero := RootRetainedAsymp.rank_zero_of_unmatchable (stagesFrom I (stage.val+1)) (insert stage old) obstructed
    have bound : errorRank I (stagesFrom I stage.val) old ≤ 1 := by
      rw [RootRetainedAsymp.rank_suffix_step stage old healthy,badZero,add_zero]
      exact min_le_right _ _
    have finite : errorRank I (stagesFrom I stage.val) old ≠ ⊤ := by
      intro infinite
      rw [infinite] at bound
      exact ENat.top_ne_natCast 1 (top_le_iff.mp bound).symm
    cases parent : rankIndex I stage.val old with
    | none => exact (finite ((RootRetainedQueries.rankQueryCorrect I stage.val old).1.mp parent)).elim
    | some depth => simp [rankCase,parent,obstructed]

theorem infiniteRank_child_matchable (stage : I.Stage) (old : Finset I.Stage) (healthy : Healthy I stage.val old)
    (infinite : rankCase I stage old = some .infiniteRank) : Matchable I (insert stage old) := by
  by_contra obstructed
  have noTool := (rankCase_noTool_iff stage old healthy).mpr obstructed
  rw [infinite] at noTool
  cases noTool

theorem cacheTarget_none_infinite (stage : I.Stage) (cache : BudgetCache I)
    (healthy : Healthy I stage.val cache.errors) (valid : ReferenceBudgetValid cache.risk)
    (none : cacheTarget I stage cache = none) : rankCase I stage cache.errors = some .infiniteRank := by
  obtain ⟨kind,query,_noTool⟩ := PRetAlignment.rankCase_exists stage cache.errors healthy
  rw [cacheTarget_eq stage cache valid,query] at none
  cases kind with
  | infiniteRank => exact query
  | noTool | finiteBad depth => cases none

end PRetRiskMassFlow
