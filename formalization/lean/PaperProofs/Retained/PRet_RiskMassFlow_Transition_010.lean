module

public import PaperProofs.Retained.PRet_RiskMassFlow_ErrorMass_009
public import PaperProofs.Retained.PRet_RiskMassFlow_Rank_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory
open scoped ENNReal

namespace PRetRiskMassFlow

variable {I : Instance}

theorem nextEntry_has_advance (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (sample : Unit × input.World) (stage nextStage : I.Stage)
    (successor : nextStage.val = stage.val+1) (history : List (VisibleEvent I))
    (entered : entryHistory input C .uncapped accounting (retainedRule input budget none) nextStage sample = some history) :
    ∃ (n : ℕ) (state next : State I),
      Prefix input C .uncapped accounting (retainedRule input budget none) sample.1
        (input.truthAt sample.2) (worldTapes input sample.2) n state ∧
      run input C .uncapped accounting (retainedRule input budget none) sample n = state ∧
      Step input C .uncapped accounting (worldTapes input sample.2) state (.advance stage) next ∧
      retainedRule input budget none sample.1 state.history = .advance stage ∧ next.history = history := by
  obtain ⟨n,cursor,first,seen⟩ :=
    (entryHistory_some_iff input C .uncapped accounting (retainedRule input budget none) nextStage sample history).mp entered
  cases n with
  | zero => change 0 = nextStage.val at cursor; omega
  | succ n =>
    have legal := retainedRule_uncapped_legal input C hretained accounting budget none
    have active : (run input C .uncapped accounting (retainedRule input budget none) sample n).halted = false := by
      apply Bool.eq_false_iff.mpr
      intro halted
      rw [run_succ_of_halted input C .uncapped accounting (retainedRule input budget none) sample n halted] at cursor
      exact first n (Nat.lt_succ_self n) cursor
    have path := run_prefix_of_active input C .uncapped accounting (retainedRule input budget none) legal sample n active
    obtain ⟨next,step⟩ := legal sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n _ path active
    have eq := run_succ_of_step input C .uncapped accounting (retainedRule input budget none) sample n next active step
    rw [eq] at cursor seen
    generalize action : retainedRule input budget none sample.1
      (run input C .uncapped accounting (retainedRule input budget none) sample n).history = selected at step
    cases step with
    | review | write | allocate | execute | stop | abandon => exact (first n (Nat.lt_succ_self n) cursor).elim
    | advance current live written resources =>
      have same : current = stage := by
        apply Fin.ext
        change (run input C .uncapped accounting (retainedRule input budget none) sample n).cursor+1 = nextStage.val at cursor
        have oldCursor := live.2
        omega
      subst current
      exact ⟨n,_,_,path,rfl,.advance _ stage live written resources,action,seen⟩

theorem replayStep_budget_update (history : List (VisibleEvent I)) (cache child : BudgetCache I)
    (stage : I.Stage) (kind : ReferenceBudgetCase) (error : Bool)
    (report : reportedError history stage = some error) (query : rankCase I stage cache.errors = some kind)
    (step : replayBudgetStep I history cache stage = some child) :
    referenceBudgetStep kind error cache.risk = some child.risk := by
  classical
  unfold replayBudgetStep at step
  obtain ⟨actualError,reported,rest⟩ := Option.bind_eq_some_iff.mp step
  have errorEq : actualError = error := Option.some.inj (reported.symm.trans report)
  subst actualError
  obtain ⟨actualKind,queried,rest⟩ := Option.bind_eq_some_iff.mp rest
  have kindEq : actualKind = kind := Option.some.inj (queried.symm.trans query)
  subst actualKind
  obtain ⟨risk,update,rest⟩ := Option.bind_eq_some_iff.mp rest
  by_cases matchable : Matchable I (if error then insert stage cache.errors else cache.errors)
  · rw [ite_eq_left matchable] at rest
    have eq := congrArg BudgetCache.risk (Option.some.inj rest)
    exact update.trans (congrArg some eq)
  · rw [ite_eq_right matchable] at rest
    cases rest

theorem prefix_reported_true_wrong (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (budget : ℚ) (sample : Unit × input.World) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n state) (stage : I.Stage)
    (report : reportedError state.history stage = some true) :
    state.ledger.written stage = some (!state.ledger.truth stage) := by
  rw [PRetActualReportedErrors048.prefix_reportedError input C hearly .uncapped accounting
    (retainedRule input budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) path stage] at report
  cases written : state.ledger.written stage with
  | none => rw [written] at report; cases report
  | some bit => cases bit <;> cases truth : state.ledger.truth stage <;> simp_all

set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine original old-H cache successor at a real next entry. Both
cache errors and the exact Option budget step are preserved. -/
theorem nextEntry_cache_transition (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (stage nextStage : I.Stage) (successor : nextStage.val = stage.val+1)
    (sample : Unit × input.World) (history nextHistory : List (VisibleEvent I))
    (entered : sample ∈ entryEvent input C accounting budget stage history)
    (nextEntered : entryHistory input C .uncapped accounting (retainedRule input budget none) nextStage sample = some nextHistory) :
    ∃ (cache child : BudgetCache I) (kind : ReferenceBudgetCase) (error : Bool),
      replayBudget I budget history stage.val = some cache ∧ replayBudget I budget nextHistory nextStage.val = some child ∧
      Healthy I stage.val cache.errors ∧ ReferenceBudgetValid cache.risk ∧
      Healthy I nextStage.val child.errors ∧ ReferenceBudgetValid child.risk ∧
      rankCase I stage cache.errors = some kind ∧ referenceBudgetStep kind error cache.risk = some child.risk ∧
      child.errors = (if error then insert stage cache.errors else cache.errors) ∧
      (error = true → sample ∈ writeError input C accounting budget stage) := by
  obtain ⟨n,state,next,path,runEq,advance,selected,seen⟩ :=
    nextEntry_has_advance input C hretained accounting budget sample stage nextStage successor nextHistory nextEntered
  cases advance with
  | advance stage live written resources =>
    obtain ⟨origin,originEntry,replayEq,_progress⟩ :=
      prefix_testing_origin input C hretained accounting budget positive small sample path live.1 stage live.2
    have same : origin = history := Option.some.inj (originEntry.symm.trans entered)
    subst origin
    obtain ⟨cache,kind,replay,healthy,valid,query,_risk,_kind,_target⟩ :=
      entry_cache input C hretained accounting budget positive small stage sample history entered
    have currentReplay : replayBudget I budget state.history stage.val = some cache := replayEq.symm.trans replay
    have historyActive : historyHalted state.history = false :=
      (prefix_historyHalted input C .uncapped accounting (retainedRule input budget none) sample.1 _ _ path).trans live.1
    have historyCursor : historyCursor state.history = stage.val :=
      (prefix_historyCursor input C .uncapped accounting (retainedRule input budget none) sample.1 _ _ path).trans live.2
    obtain ⟨actual,error,actualReplay,_actualHealthy,_actualValid,report,matchable⟩ :=
      PRetAlignment.rule_advance input budget none sample.1 state.history stage historyActive historyCursor selected
    have actualEq : actual = cache := Option.some.inj (actualReplay.symm.trans currentReplay)
    subst actual
    obtain ⟨child,childStep,childHealthy,childValid,childErrors⟩ :=
      PRetAlignment.replayStep_exists state.history cache stage healthy valid error report matchable
    have actualStep : Step input C .uncapped accounting (worldTapes input sample.2) state
        (retainedRule input budget none sample.1 state.history)
        (record accounting state (.advance stage) [.advanced stage] (advanceLedger state stage) (state.cursor+1) false) := by
      rw [selected]
      exact .advance state stage live written resources
    have frame := PRetAlignment.step_replayBudget_past input C hretained.1 .uncapped accounting
      (retainedRule input budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) path actualStep budget
    have reportFrame := PRetAlignment.step_reportedError_of_written input C hretained.1 .uncapped accounting
      (retainedRule input budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) path actualStep stage rfl
    change reportedError (state.history ++ [.advanced stage]) stage = reportedError state.history stage at reportFrame
    have nextReplay : replayBudget I budget nextHistory nextStage.val = some child := by
      rw [← seen,successor,PRetBudgetReplay117.replayBudget_succ]
      change ((replayBudget I budget (state.history ++ [.advanced stage]) stage.val).bind
        (fun cache => replayBudgetStep I (state.history ++ [.advanced stage]) cache stage)) = some child
      have oldFrame : replayBudget I budget (state.history ++ [.advanced stage]) stage.val = some cache := by
        rw [← live.2] at currentReplay ⊢
        exact frame.trans currentReplay
      rw [oldFrame]
      change replayBudgetStep I (state.history ++ [.advanced stage]) cache stage = some child
      rw [PRetBudgetReplay117.replayStep_congr _ state.history cache stage reportFrame]
      exact childStep
    refine ⟨cache,child,kind,error,replay,nextReplay,healthy,valid,?_,childValid,query,
      replayStep_budget_update state.history cache child stage kind error report query childStep,childErrors,?_⟩
    · simpa only [successor] using childHealthy
    · intro errorTrue
      have wrong := prefix_reported_true_wrong input C hretained.1 accounting budget sample path stage (errorTrue ▸ report)
      refine ⟨n,?_⟩
      rw [runEq]
      exact wrong

end PRetRiskMassFlow
