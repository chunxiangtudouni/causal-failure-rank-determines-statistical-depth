module

public import PaperProofs.Retained.PRet_RiskMassFlow_Realization_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory

namespace PRetRiskMassFlow

variable {I : Instance}

theorem testing_target_action_cases (input : StatisticalInput I) (history : List (VisibleEvent I)) (cache : BudgetCache I)
    (stage : I.Stage) (kind : ReferenceBudgetCase) (p : ℚ)
    (query : rankCase I stage cache.errors = some kind) (chosen : referenceBudgetTarget kind cache.risk = some p)
    (alphabet : ∀ symbol ∈ historyObservations history stage, symbol < (input.experiment stage).alphabetSize) :
    retainedTestingAction input none history cache stage = .review stage ∨
      ∃ bit,retainedTestingAction input none history cache stage = .write stage bit := by
  have eq := testing_at_target input history cache stage kind p query chosen
  rw [dite_eq_left alphabet] at eq
  by_cases hit : (input.experiment stage).rationalWordHits p (historyObservationWord input history stage alphabet) = true
  · rw [ite_eq_left hit] at eq
    exact Or.inr ⟨_,eq⟩
  · rw [ite_eq_right hit] at eq
    exact Or.inl eq

theorem testing_action_cases (input : StatisticalInput I) (history : List (VisibleEvent I)) (cache : BudgetCache I)
    (stage : I.Stage) (healthy : Healthy I stage.val cache.errors)
    (alphabet : ∀ symbol ∈ historyObservations history stage, symbol < (input.experiment stage).alphabetSize) :
    retainedTestingAction input none history cache stage = .review stage ∨
      ∃ bit,retainedTestingAction input none history cache stage = .write stage bit := by
  obtain ⟨kind,query,_noTool⟩ := PRetAlignment.rankCase_exists stage cache.errors healthy
  cases kind with
  | infiniteRank => exact Or.inr ⟨false,by simp only [retainedTestingAction,query]⟩
  | noTool | finiteBad depth => exact testing_target_action_cases input history cache stage _ _ query rfl alphabet

theorem prefix_candidate_step_on_open (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) seed truth tapes n state)
    (active : state.halted = false) (stage : I.Stage) (cursor : state.cursor = stage.val)
    (openPort : state.ledger.written stage = none) :
    ∃ next,Step input C .uncapped accounting tapes state (retainedCandidate input budget none state.history) next ∧
      retainedCandidate input budget none state.history ≠ .abandon := by
  obtain ⟨cache,_replay,healthy,_valid,candidate,_targetEq⟩ :=
    prefix_open_testing input C hearly accounting budget positive small seed truth tapes path active stage cursor openPort
  have alphabet : ∀ symbol ∈ historyObservations state.history stage, symbol < (input.experiment stage).alphabetSize :=
    fun symbol member => prefix_historyObservation_alphabet input C .uncapped accounting (retainedRule input budget none)
      seed truth tapes path stage symbol member
  rcases testing_action_cases input state.history cache stage healthy alphabet with review | ⟨bit,write⟩
  · have selected := candidate.trans review
    refine ⟨record accounting state (.review stage) [.observation stage (tapes stage (state.ledger.reviews stage).toNat).val]
      (reviewLedger state stage) state.cursor false,?_,?_⟩
    · rw [selected]
      exact Step.review state stage ⟨active,cursor⟩ openPort (Or.inl rfl)
    · rw [selected]
      intro impossible
      cases impossible
  · have selected := candidate.trans write
    refine ⟨record accounting state (.write stage bit) (writeResponses C state stage bit)
      (reportedWriteLedger C state stage bit) state.cursor false,?_,?_⟩
    · rw [selected]
      exact Step.write state stage bit ⟨active,cursor⟩ openPort (Or.inl rfl)
    · rw [selected]
      intro impossible
      cases impossible

theorem prefix_rule_ne_abandon_on_open (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) seed truth tapes n state)
    (active : state.halted = false) (stage : I.Stage) (cursor : state.cursor = stage.val)
    (openPort : state.ledger.written stage = none) :
    retainedRule input budget none seed state.history = retainedCandidate input budget none state.history ∧
      retainedRule input budget none seed state.history ≠ .abandon := by
  obtain ⟨next,step,notAbandon⟩ := prefix_candidate_step_on_open input C hearly accounting budget positive small
    seed truth tapes path active stage cursor openPort
  have pass := PRetRetainedGuard007.guarded_action_of_step input C hearly accounting
    (fun (_ : Unit) history => retainedCandidate input budget none history) seed truth tapes path step
  have same : retainedRule input budget none seed state.history = retainedCandidate input budget none state.history := pass
  exact ⟨same,fun rejected => notAbandon (same.symm.trans rejected)⟩

end PRetRiskMassFlow
