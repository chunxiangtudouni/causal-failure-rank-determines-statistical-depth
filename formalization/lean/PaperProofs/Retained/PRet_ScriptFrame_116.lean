module

public import PaperProofs.Retained.CompletedQualification

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetScriptFrame116

open Common Common.Native Statistics

variable {I : Instance}

/-- The actual retained testing script never allocates or executes a tool. -/
theorem testing_no_correction (input : StatisticalInput I) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) (cache : BudgetCache I) (stage : I.Stage)
    (handle : MismatchHandle I) (tool : I.Tool) :
    retainedTestingAction input limit history cache stage ≠ .allocate handle tool ∧
      retainedTestingAction input limit history cache stage ≠ .execute handle tool := by
  cases hk : rankCase I stage cache.errors with
  | none =>
    simp only [retainedTestingAction, hk]
    constructor <;> intro ha <;> cases ha
  | some kind =>
    cases kind with
    | infiniteRank =>
      simp only [retainedTestingAction, hk]
      constructor <;> intro ha <;> cases ha
    | noTool | finiteBad depth =>
      simp only [retainedTestingAction, hk, Option.bind_some, referenceBudgetTarget]
      by_cases hv : ∀ symbol ∈ historyObservations history stage, symbol < (input.experiment stage).alphabetSize
      · rw [dite_eq_left hv]
        split_ifs
        · constructor <;> intro ha <;> cases ha
        · cases limit with
          | none =>
            change Action.review stage ≠ .allocate handle tool ∧ Action.review stage ≠ .execute handle tool
            constructor <;> intro ha <;> cases ha
          | some quota =>
            change (if (historyObservations history stage).length < quota stage then Action.review stage else .abandon) ≠ .allocate handle tool ∧
              (if (historyObservations history stage).length < quota stage then Action.review stage else .abandon) ≠ .execute handle tool
            by_cases hq : (historyObservations history stage).length < quota stage
            · rw [ite_eq_left hq]
              constructor <;> intro ha <;> cases ha
            · rw [ite_eq_right hq]
              constructor <;> intro ha <;> cases ha
      · rw [dite_eq_right hv]
        constructor <;> intro ha <;> cases ha

/-- No real candidate correction is issued before the terminal cursor. -/
theorem candidate_no_correction (input : StatisticalInput I) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) (hbefore : historyCursor history < I.stageCount)
    (handle : MismatchHandle I) (tool : I.Tool) :
    retainedCandidate input budget limit history ≠ .allocate handle tool ∧
      retainedCandidate input budget limit history ≠ .execute handle tool := by
  unfold retainedCandidate
  split
  · constructor <;> intro ha <;> cases ha
  · dsimp only
    split
    · constructor <;> intro ha <;> cases ha
    · split
      · constructor <;> intro ha <;> cases ha
      · split
        · exact testing_no_correction input limit history _ _ handle tool
        · split
          · constructor <;> intro ha <;> cases ha
          · split_ifs <;> constructor <;> intro ha <;> cases ha

theorem rule_no_correction (input : StatisticalInput I) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (seed : Unit) (history : List (VisibleEvent I)) (hbefore : historyCursor history < I.stageCount)
    (handle : MismatchHandle I) (tool : I.Tool) :
    retainedRule input budget limit seed history ≠ .allocate handle tool ∧
      retainedRule input budget limit seed history ≠ .execute handle tool := by
  unfold retainedRule PRetRetainedGuard007.guarded
  split_ifs
  · exact candidate_no_correction input budget limit history hbefore handle tool
  · constructor <;> intro ha <;> cases ha

/-- True all-Prefix terminal-only frame of THIS retained script, including
failed/abandoned prefixes, independently of any risk/cost/cap assumption. -/
theorem prefix_no_corrections (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting (retainedRule input budget limit) seed truth tapes n s)
    (hbefore : s.cursor < I.stageCount) : s.ledger.commitments = [] ∧ s.ledger.executions = [] := by
  revert hbefore
  induction hp with
  | initial => intro _; exact ⟨rfl, rfl⟩
  | @next n s next earlier step ih =>
    intro hbefore
    have hold := lt_of_le_of_lt (step_cursor_bounds input C mode accounting tapes step).1 hbefore
    have hnil := ih hold
    have hc : historyCursor s.history < I.stageCount := by
      rw [prefix_historyCursor input C mode accounting (retainedRule input budget limit) seed truth tapes earlier]
      exact hold
    generalize haction : retainedRule input budget limit seed s.history = action at step
    cases step with
    | allocate handle tool active valid compatible unused unallocated window resources =>
      exact False.elim ((rule_no_correction input budget limit seed s.history hc handle tool).1 haction)
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      exact False.elim ((rule_no_correction input budget limit seed s.history hc handle tool).2 haction)
    | write stage bit live port resources =>
      change (reportedWriteLedger C s stage bit).commitments = [] ∧ (reportedWriteLedger C s stage bit).executions = []
      simp only [reportedWriteLedger]
      split_ifs <;> exact hnil
    | review | advance | stop | abandon => exact hnil

theorem terminalOnly (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (limit : ReferenceObservationLimit I) :
    TerminalOnly input C .uncapped accounting (retainedRule input budget limit) := by
  intro seed truth tapes n s hp hbefore
  exact prefix_no_corrections input C .uncapped accounting budget limit seed truth tapes hp hbefore

end PaperProofs.Retained.PRetScriptFrame116
