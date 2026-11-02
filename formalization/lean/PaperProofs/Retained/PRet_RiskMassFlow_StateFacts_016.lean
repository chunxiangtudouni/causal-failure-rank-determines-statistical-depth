module

public import PaperProofs.Retained.PRet_RiskMassFlow_OpenSteps_015
public import PaperProofs.Retained.PRet_RiskMassFlow_Transition_010
public import PaperProofs.Retained.PRet_PastWritten_015

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory

namespace PRetRiskMassFlow

variable {I : Instance}

theorem prefix_cache_at_cursor (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) seed truth tapes n state) :
    ∃ cache,replayBudget I budget state.history state.cursor = some cache ∧ Healthy I state.cursor cache.errors ∧
      ReferenceBudgetValid cache.risk ∧ cache.errors = reportedErrors I state.history state.cursor := by
  obtain ⟨cache,replay⟩ := PRetAlignment.prefix_replay_exists input C hearly accounting budget none seed truth tapes path
  have bound := (prefix_cursorInvariant input C .uncapped accounting (retainedRule input budget none) seed truth tapes path).bound
  have initialValid : ReferenceBudgetValid (budget/2) := by constructor <;> linarith
  obtain ⟨healthy,valid,errors⟩ := PRetAlignment.replayBudget_sound budget state.history initialValid state.cursor bound cache replay
  exact ⟨cache,replay,healthy,valid,errors⟩

theorem prefix_matchable_at_terminal (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) seed truth tapes n state)
    (cursor : state.cursor = I.stageCount) : Matchable I (ordinaryMismatches state.ledger) := by
  obtain ⟨cache,_replay,healthy,_valid,errors⟩ :=
    prefix_cache_at_cursor input C hearly accounting budget positive small seed truth tapes path
  rw [cursor,PRetCompletion.reportedErrors_full input C hearly accounting (retainedRule input budget none)
    seed truth tapes path] at errors
  rw [← errors]
  exact healthy.2.2

theorem prefix_allWritten_at_terminal (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) seed truth tapes n state)
    (cursor : state.cursor = I.stageCount) : allWritten state.ledger := by
  intro stage
  apply PRetPastWritten015.prefix_past_written input C .uncapped accounting (retainedRule input budget none) seed truth tapes path stage
  rw [cursor]
  exact stage.isLt

theorem candidate_at_reported (input : StatisticalInput I) (budget : ℚ) (history : List (VisibleEvent I))
    (stage : I.Stage) (cache : BudgetCache I) (active : historyHalted history = false)
    (cursor : historyCursor history = stage.val) (replay : replayBudget I budget history stage.val = some cache)
    (healthy : Healthy I stage.val cache.errors) (valid : ReferenceBudgetValid cache.risk)
    (pair : Bool × ℕ) (written : historyWrite history stage = some pair) (error : Bool)
    (report : reportedError history stage = some error) :
    retainedCandidate input budget none history =
      if Matchable I (if error then insert stage cache.errors else cache.errors) then .advance stage else .abandon := by
  have before : historyCursor history < I.stageCount := cursor ▸ stage.isLt
  have same : (⟨historyCursor history,before⟩ : I.Stage) = stage := Fin.ext cursor
  unfold retainedCandidate
  simp only [active,Bool.false_eq_true,↓reduceIte,dite_eq_left before,same]
  rw [cursor,replay]
  dsimp only
  have good : ¬(¬Healthy I stage.val cache.errors ∨ ¬(0<cache.risk ∧ cache.risk≤1/4)) :=
    not_or.mpr ⟨not_not.mpr healthy,not_not.mpr valid⟩
  rw [ite_eq_right good,written]
  dsimp only
  rw [report]

theorem testing_not_stop (input : StatisticalInput I) (history : List (VisibleEvent I)) (cache : BudgetCache I)
    (stage : I.Stage) : retainedTestingAction input none history cache stage ≠ .stop := by
  cases query : rankCase I stage cache.errors with
  | none => simp only [retainedTestingAction,query]; intro selected; cases selected
  | some kind =>
    cases kind with
    | infiniteRank => simp only [retainedTestingAction,query]; intro selected; cases selected
    | noTool | finiteBad depth =>
      simp only [retainedTestingAction,query,Option.bind_some,referenceBudgetTarget]
      by_cases alphabet : ∀ symbol ∈ historyObservations history stage,symbol < (input.experiment stage).alphabetSize
      · rw [dite_eq_left alphabet]
        split_ifs <;> intro selected <;> cases selected
      · rw [dite_eq_right alphabet]
        intro selected
        cases selected

set_option backward.isDefEq.respectTransparency.types false in
theorem candidate_stage_not_stop (input : StatisticalInput I) (budget : ℚ) (history : List (VisibleEvent I))
    (stage : I.Stage) (active : historyHalted history = false) (cursor : historyCursor history = stage.val) :
    retainedCandidate input budget none history ≠ .stop := by
  have before : historyCursor history < I.stageCount := cursor ▸ stage.isLt
  have same : (⟨historyCursor history,before⟩ : I.Stage) = stage := Fin.ext cursor
  unfold retainedCandidate
  simp only [active,Bool.false_eq_true,↓reduceIte,dite_eq_left before,same]
  rw [cursor]
  cases replay : replayBudget I budget history stage.val with
  | none => intro selected; cases selected
  | some cache =>
    dsimp only
    by_cases invalid : ¬Healthy I stage.val cache.errors ∨ ¬(0<cache.risk ∧ cache.risk≤1/4)
    · rw [ite_eq_left invalid]
      intro selected
      cases selected
    · rw [ite_eq_right invalid]
      cases written : historyWrite history stage with
      | none => exact testing_not_stop input history cache stage
      | some pair =>
        dsimp only
        cases report : reportedError history stage with
        | none => intro selected; cases selected
        | some error =>
          dsimp only
          split_ifs <;> intro selected <;> cases selected

theorem candidate_before_not_stop (input : StatisticalInput I) (budget : ℚ) (history : List (VisibleEvent I))
    (active : historyHalted history = false) (before : historyCursor history < I.stageCount) :
    retainedCandidate input budget none history ≠ .stop :=
  candidate_stage_not_stop input budget history ⟨historyCursor history,before⟩ active rfl

end PRetRiskMassFlow
