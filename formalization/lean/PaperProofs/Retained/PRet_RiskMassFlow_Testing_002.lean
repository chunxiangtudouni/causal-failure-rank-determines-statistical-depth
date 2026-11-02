module

public import PaperProofs.Retained.PRet_RiskMassFlow_Target_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory

namespace PRetRiskMassFlow

variable {I : Instance}

theorem testing_at_target (input : StatisticalInput I) (history : List (VisibleEvent I)) (cache : BudgetCache I)
    (stage : I.Stage) (kind : ReferenceBudgetCase) (p : ℚ)
    (query : rankCase I stage cache.errors = some kind) (chosen : referenceBudgetTarget kind cache.risk = some p) :
    retainedTestingAction input none history cache stage =
      if hv : ∀ symbol ∈ historyObservations history stage, symbol < (input.experiment stage).alphabetSize then
        if (input.experiment stage).rationalWordHits p (historyObservationWord input history stage hv) then
          .write stage ((input.experiment stage).rationalWordMAP (historyObservationWord input history stage hv))
        else .review stage
      else .abandon := by
  cases kind with
  | infiniteRank => cases chosen
  | noTool | finiteBad depth =>
    simp only [retainedTestingAction,query,Option.bind_some,chosen]

theorem testing_review_nonhit (input : StatisticalInput I) (history : List (VisibleEvent I)) (cache : BudgetCache I)
    (stage : I.Stage) (valid : ReferenceBudgetValid cache.risk)
    (selected : retainedTestingAction input none history cache stage = .review stage) :
    ∃ p, cacheTarget I stage cache = some p ∧
      ∀ hv : ∀ symbol ∈ historyObservations history stage, symbol < (input.experiment stage).alphabetSize,
        (input.experiment stage).rationalWordHits p (historyObservationWord input history stage hv) = false := by
  cases query : rankCase I stage cache.errors with
  | none => simp only [retainedTestingAction,query] at selected; cases selected
  | some kind =>
    have finiteTarget : ∃ p, referenceBudgetTarget kind cache.risk = some p := by
      cases kind with
      | infiniteRank => simp only [retainedTestingAction,query] at selected; cases selected
      | noTool | finiteBad depth => exact ⟨_,rfl⟩
    obtain ⟨p,chosen⟩ := finiteTarget
    have target : cacheTarget I stage cache = some p := by
      rw [cacheTarget_eq stage cache valid,query]
      exact chosen
    rw [testing_at_target input history cache stage kind p query chosen] at selected
    by_cases hv : ∀ symbol ∈ historyObservations history stage, symbol < (input.experiment stage).alphabetSize
    · rw [dite_eq_left hv] at selected
      by_cases hit : (input.experiment stage).rationalWordHits p (historyObservationWord input history stage hv) = true
      · rw [ite_eq_left hit] at selected
        cases selected
      · exact ⟨p,target,fun _ => Bool.eq_false_iff.mpr hit⟩
    · rw [dite_eq_right hv] at selected
      cases selected

theorem testing_write_hit (input : StatisticalInput I) (history : List (VisibleEvent I)) (cache : BudgetCache I)
    (stage : I.Stage) (p : ℚ) (bit : Bool) (target : cacheTarget I stage cache = some p)
    (hv : ∀ symbol ∈ historyObservations history stage, symbol < (input.experiment stage).alphabetSize)
    (selected : retainedTestingAction input none history cache stage = .write stage bit) :
    (input.experiment stage).rationalWordHits p (historyObservationWord input history stage hv) = true ∧
      bit = (input.experiment stage).rationalWordMAP (historyObservationWord input history stage hv) := by
  unfold cacheTarget at target
  by_cases valid : 0 < cache.risk ∧ cache.risk ≤ 1/4
  · rw [ite_eq_left valid] at target
    obtain ⟨kind,query,chosen⟩ := Option.bind_eq_some_iff.mp target
    rw [testing_at_target input history cache stage kind p query chosen,dite_eq_left hv] at selected
    by_cases hit : (input.experiment stage).rationalWordHits p (historyObservationWord input history stage hv) = true
    · rw [ite_eq_left hit] at selected
      exact ⟨hit,(Action.write.inj selected).2.symm⟩
    · rw [ite_eq_right hit] at selected
      cases selected
  · rw [ite_eq_right valid] at target
    cases target

theorem prefix_open_testing (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) seed truth tapes n state)
    (active : state.halted = false) (stage : I.Stage) (cursor : state.cursor = stage.val)
    (openPort : state.ledger.written stage = none) :
    ∃ cache, replayBudget I budget state.history stage.val = some cache ∧
      Healthy I stage.val cache.errors ∧ ReferenceBudgetValid cache.risk ∧
      retainedCandidate input budget none state.history = retainedTestingAction input none state.history cache stage ∧
      entryTarget I budget stage state.history = cacheTarget I stage cache := by
  obtain ⟨cache,replay⟩ := PRetAlignment.prefix_replay_exists input C hearly accounting budget none seed truth tapes path
  rw [cursor] at replay
  have initialValid : ReferenceBudgetValid (budget/2) := by constructor <;> linarith
  obtain ⟨healthy,valid,_errors⟩ := PRetAlignment.replayBudget_sound budget state.history initialValid stage.val
    (Nat.le_of_lt stage.isLt) cache replay
  have historyOpen : historyWrite state.history stage = none := by
    rw [prefix_historyWrite input C .uncapped accounting (retainedRule input budget none) seed truth tapes path stage,openPort]
    rfl
  have historyActive : historyHalted state.history = false :=
    (prefix_historyHalted input C .uncapped accounting (retainedRule input budget none) seed truth tapes path).trans active
  have historyCursor : historyCursor state.history = stage.val :=
    (prefix_historyCursor input C .uncapped accounting (retainedRule input budget none) seed truth tapes path).trans cursor
  exact ⟨cache,replay,healthy,valid,candidate_at_open input budget state.history stage cache historyActive historyCursor
    replay healthy valid historyOpen,entryTarget_eq budget stage state.history cache replay⟩

end PRetRiskMassFlow
