module

public import PaperProofs.Retained.PRet_Alignment_PastFrame_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics

namespace PRetAlignment

variable {I : Instance}

theorem testing_not_advance (input : StatisticalInput I) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) (cache : BudgetCache I) (stage target : I.Stage) :
    retainedTestingAction input limit history cache stage ≠ .advance target := by
  cases hk : rankCase I stage cache.errors with
  | none =>
    simp only [retainedTestingAction, hk]
    intro action
    cases action
  | some kind =>
    cases kind with
    | infiniteRank =>
      simp only [retainedTestingAction, hk]
      intro action
      cases action
    | noTool | finiteBad depth =>
      simp only [retainedTestingAction, hk, Option.bind_some, referenceBudgetTarget]
      by_cases hv : ∀ symbol ∈ historyObservations history stage, symbol < (input.experiment stage).alphabetSize
      · rw [dite_eq_left hv]
        split_ifs
        · intro action; cases action
        · cases limit with
          | none => intro action; cases action
          | some quota =>
            change (if (historyObservations history stage).length < quota stage then Action.review stage else .abandon) ≠ .advance target
            split_ifs <;> intro action <;> cases action
      · rw [dite_eq_right hv]
        intro action
        cases action

theorem candidate_advance (input : StatisticalInput I) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) (stage : I.Stage)
    (hhalt : historyHalted history = false) (hcursor : historyCursor history = stage.val)
    (action : retainedCandidate input budget limit history = .advance stage) :
    ∃ cache error, replayBudget I budget history stage.val = some cache ∧
      Healthy I stage.val cache.errors ∧ ReferenceBudgetValid cache.risk ∧
      reportedError history stage = some error ∧
      Matchable I (if error then insert stage cache.errors else cache.errors) := by
  classical
  have before : historyCursor history < I.stageCount := hcursor ▸ stage.isLt
  have eq : (⟨historyCursor history,before⟩ : I.Stage) = stage := Fin.ext hcursor
  unfold retainedCandidate at action
  simp only [hhalt, Bool.false_eq_true, ↓reduceIte, dite_eq_left before, eq] at action
  rw [hcursor] at action
  cases replay : replayBudget I budget history stage.val with
  | none => rw [replay] at action; cases action
  | some cache =>
    rw [replay] at action
    dsimp only at action
    by_cases invalid : ¬Healthy I stage.val cache.errors ∨ ¬(0 < cache.risk ∧ cache.risk ≤ 1/4)
    · rw [ite_eq_left invalid] at action
      cases action
    · rw [ite_eq_right invalid] at action
      have valid : Healthy I stage.val cache.errors ∧ ReferenceBudgetValid cache.risk :=
        ⟨not_not.mp (not_or.mp invalid).1, not_not.mp (not_or.mp invalid).2⟩
      cases write : historyWrite history stage with
      | none =>
        rw [write] at action
        exact (testing_not_advance input limit history cache stage stage action).elim
      | some pair =>
        rw [write] at action
        dsimp only at action
        cases report : reportedError history stage with
        | none => rw [report] at action; cases action
        | some error =>
          rw [report] at action
          dsimp only at action
          by_cases matchable : Matchable I (if error then insert stage cache.errors else cache.errors)
          · exact ⟨cache,error,rfl,valid.1,valid.2,rfl,matchable⟩
          · rw [ite_eq_right matchable] at action
            cases action

theorem rule_advance (input : StatisticalInput I) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (seed : Unit) (history : List (VisibleEvent I)) (stage : I.Stage)
    (hhalt : historyHalted history = false) (hcursor : historyCursor history = stage.val)
    (action : retainedRule input budget limit seed history = .advance stage) :
    ∃ cache error, replayBudget I budget history stage.val = some cache ∧
      Healthy I stage.val cache.errors ∧ ReferenceBudgetValid cache.risk ∧
      reportedError history stage = some error ∧
      Matchable I (if error then insert stage cache.errors else cache.errors) := by
  unfold retainedRule PRetRetainedGuard007.guarded at action
  split at action
  · exact candidate_advance input budget limit history stage hhalt hcursor action
  · cases action

end PRetAlignment
