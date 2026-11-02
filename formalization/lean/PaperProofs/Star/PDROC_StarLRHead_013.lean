module

public import PaperProofs.Common.ReferenceObservationCost

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native

namespace PDROC.StarLocalReview

variable {I : Instance}

theorem nextFromFrontier_preserves (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (state : State I)
    (action : Action I) (frontier : Frontier input) (property : State I → Prop)
    (initial : property state)
    (valid : ∀ next, Step input C mode accounting (frozenTapes input frontier) state action next → property next)
    (invalid : property (stopState state true)) :
    property (nextFromFrontier input C mode accounting state action frontier) := by
  classical
  unfold nextFromFrontier
  split
  · exact initial
  · split
    · rename_i existsStep
      exact valid _ (Classical.choose_spec existsStep)
    · exact invalid

theorem step_reviews_eq_of_written (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {state next : State I} {action : Action I}
    (step : Step input C mode accounting tapes state action next) (stage : I.Stage)
    (bit : Bool) (written : state.ledger.written stage = some bit) :
    next.ledger.reviews stage = state.ledger.reviews stage := by
  cases step with
  | review current live port resources =>
    have distinct : stage ≠ current := by
      intro equal
      subst current
      rw [port] at written
      cases written
    simp only [record, reviewLedger, Function.update_of_ne distinct]
  | write current chosen live port resources =>
    classical
    simp only [record, reportedWriteLedger]
    split_ifs <;> rfl
  | allocate | execute | advance | stop | abandon => rfl

theorem nextFromFrontier_reviews_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (state : State I)
    (action : Action I) (frontier : Frontier input) (stage : I.Stage) :
    state.ledger.reviews stage ≤
      (nextFromFrontier input C mode accounting state action frontier).ledger.reviews stage := by
  apply nextFromFrontier_preserves input C mode accounting state action frontier
    (fun next => state.ledger.reviews stage ≤ next.ledger.reviews stage)
  · exact le_rfl
  · intro next step
    exact step_reviews_mono input C mode accounting _ step stage
  · exact le_rfl

theorem nextFromFrontier_written_some (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (state : State I)
    (action : Action I) (frontier : Frontier input) (stage : I.Stage) (bit : Bool)
    (written : state.ledger.written stage = some bit) :
    (nextFromFrontier input C mode accounting state action frontier).ledger.written stage = some bit := by
  apply nextFromFrontier_preserves input C mode accounting state action frontier
    (fun next => next.ledger.written stage = some bit)
  · exact written
  · intro next step
    exact step_written_some input C mode accounting _ step stage bit written
  · exact written

theorem nextFromFrontier_reviews_eq_of_written (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (state : State I)
    (action : Action I) (frontier : Frontier input) (stage : I.Stage) (bit : Bool)
    (written : state.ledger.written stage = some bit) :
    (nextFromFrontier input C mode accounting state action frontier).ledger.reviews stage =
      state.ledger.reviews stage := by
  apply nextFromFrontier_preserves input C mode accounting state action frontier
    (fun next => next.ledger.reviews stage = state.ledger.reviews stage)
  · rfl
  · intro next step
    exact step_reviews_eq_of_written input C mode accounting _ step stage bit written
  · rfl

theorem run_reviews_mono_no_legal {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) (stage : I.Stage) :
    Monotone (fun n => (run input C mode accounting rule sample n).ledger.reviews stage) := by
  apply monotone_nat_of_le_succ
  intro n
  exact nextFromFrontier_reviews_mono input C mode accounting _ _ _ stage

theorem run_written_after_no_legal {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) (start extra : ℕ) (stage : I.Stage) (bit : Bool)
    (written : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    (run input C mode accounting rule sample (start+extra)).ledger.written stage = some bit := by
  induction extra with
  | zero => exact written
  | succ extra ih =>
    exact nextFromFrontier_written_some input C mode accounting _ _ _ stage bit ih

theorem run_reviews_written_port_no_legal {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) (start extra : ℕ) (stage : I.Stage) (bit : Bool)
    (written : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    (run input C mode accounting rule sample (start+extra)).ledger.reviews stage =
      (run input C mode accounting rule sample start).ledger.reviews stage := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have still := run_written_after_no_legal input C mode accounting rule sample start extra stage bit written
    exact (nextFromFrontier_reviews_eq_of_written input C mode accounting _ _ _ stage bit still).trans ih

end PDROC.StarLocalReview
