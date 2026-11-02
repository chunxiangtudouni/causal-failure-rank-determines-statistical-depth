module

public import PaperProofs.Retained.RootRetainedAsymp_001
public import PaperProofs.Retained.RootRetainedQueries_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics

namespace PRetAlignment

variable {I : Instance}

theorem rankCase_exists (stage : I.Stage) (old : Finset I.Stage) (healthy : Healthy I stage.val old) :
    ∃ kind, rankCase I stage old = some kind ∧ (kind = .noTool → ¬Matchable I (insert stage old)) := by
  classical
  cases parent : rankIndex I stage.val old with
  | none =>
    refine ⟨.infiniteRank, ?_, ?_⟩
    · simp only [rankCase, parent]
    · intro impossible
      cases impossible
  | some depth =>
    by_cases matchable : Matchable I (insert stage old)
    · have parentRank := ((RootRetainedQueries.rankQueryCorrect I stage.val old).2 depth).mp parent
      have finite : errorRank I (stagesFrom I (stage.val+1)) (insert stage old) ≠ ⊤ := by
        intro top
        have bound := RootRetainedAsymp.rank_bad_le_current stage old healthy
        rw [top, parentRank] at bound
        exact ENat.top_ne_natCast depth (top_le_iff.mp bound).symm
      obtain ⟨childDepth, childRank⟩ := ENat.ne_top_iff_exists.mp finite
      have childQuery : rankIndex I (stage.val+1) (insert stage old) = some childDepth :=
        ((RootRetainedQueries.rankQueryCorrect I (stage.val+1) (insert stage old)).2 childDepth).mpr childRank.symm
      have positive : 0 < childDepth := by
        have hp := RootRetainedAsymp.rank_positive (stagesFrom I (stage.val+1)) (insert stage old) matchable
        rw [← childRank] at hp
        exact_mod_cast hp
      refine ⟨.finiteBad ⟨childDepth, positive⟩, ?_, ?_⟩
      · simp [rankCase, parent, matchable, childQuery, positive]
      · intro impossible
        cases impossible
    · refine ⟨.noTool, ?_, fun _ => matchable⟩
      simp [rankCase, parent, matchable]

theorem rankCase_step_exists (stage : I.Stage) (old : Finset I.Stage) (healthy : Healthy I stage.val old)
    (error : Bool) (risk : ℚ) (valid : ReferenceBudgetValid risk)
    (matchable : Matchable I (if error then insert stage old else old)) :
    ∃ kind child, rankCase I stage old = some kind ∧ referenceBudgetStep kind error risk = some child ∧
      ReferenceBudgetValid child := by
  obtain ⟨kind, query, noTool⟩ := rankCase_exists stage old healthy
  have next : ∃ child, referenceBudgetStep kind error risk = some child := by
    cases kind with
    | infiniteRank => exact ⟨_, rfl⟩
    | finiteBad depth => exact ⟨_, rfl⟩
    | noTool =>
      cases error with
      | false => exact ⟨_, rfl⟩
      | true => exact (noTool rfl matchable).elim
  obtain ⟨child, step⟩ := next
  exact ⟨kind, child, query, step, (referenceBudgetStep_valid_floor kind error risk child valid step).1⟩

theorem replayStep_exists (history : List (VisibleEvent I)) (cache : BudgetCache I) (stage : I.Stage)
    (healthy : Healthy I stage.val cache.errors) (valid : ReferenceBudgetValid cache.risk)
    (error : Bool) (reported : reportedError history stage = some error)
    (matchable : Matchable I (if error then insert stage cache.errors else cache.errors)) :
    ∃ next, replayBudgetStep I history cache stage = some next ∧
      Healthy I (stage.val+1) next.errors ∧ ReferenceBudgetValid next.risk ∧
      next.errors = if error then insert stage cache.errors else cache.errors := by
  classical
  obtain ⟨kind, child, query, step, childValid⟩ :=
    rankCase_step_exists stage cache.errors healthy error cache.risk valid matchable
  refine ⟨⟨if error then insert stage cache.errors else cache.errors, child⟩, ?_, ?_, childValid, rfl⟩
  · unfold replayBudgetStep
    rw [reported]
    dsimp
    rw [query]
    dsimp
    rw [step]
    dsimp
    rw [ite_eq_left matchable]
  · cases error with
    | false => exact healthy_correct I stage cache.errors healthy
    | true => exact (healthy_error_iff I stage cache.errors healthy).mpr matchable

end PRetAlignment
