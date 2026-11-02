module

public import PaperProofs.Retained.PRet_Completion_Guards_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics

namespace PRetCompletion

variable {I : Instance}

set_option backward.isDefEq.respectTransparency.types false in
theorem terminal_stop_covers (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) {Seed : Type*} (source : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C .uncapped accounting source seed truth tapes n state)
    (selected : terminalMatchingAction I state.history = .stop) :
    ordinaryMismatches state.ledger ⊆ executedStages state.ledger := by
  classical
  have noPending : pending I state.history = none := by
    unfold terminalMatchingAction at selected
    dsimp only at selected
    cases first : firstAssignment I (reportedErrors I state.history I.stageCount) with
    | none => rw [first] at selected; cases selected
    | some assignment =>
      rw [first] at selected
      change (match pending I state.history with | none => Action.stop | some stage => _) = Action.stop at selected
      cases found : pending I state.history with
      | none => rfl
      | some stage =>
        rw [found] at selected
        dsimp only at selected
        cases slot : assignment[stage.val]?.join with
        | none => rw [slot] at selected; cases visible : referenceVisibleHandle state.history stage <;> rw [visible] at selected <;> cases selected
        | some tool =>
          rw [slot] at selected
          cases visible : referenceVisibleHandle state.history stage with
          | none => rw [visible] at selected; cases selected
          | some handle =>
            rw [visible] at selected
            dsimp only at selected
            cases old : (historyCommitments state.history).find? (fun a => a.1.stage == stage) with
            | none => rw [old] at selected; cases selected
            | some pair =>
              rw [old] at selected
              dsimp only at selected
              by_cases same : pair.2 = tool
              · rw [ite_eq_left same] at selected; cases selected
              · rw [ite_eq_right same] at selected; cases selected
  intro stage wrong
  have reportedWrong : stage ∈ reportedErrors I state.history I.stageCount :=
    (reportedErrors_full input C hearly accounting source seed truth tapes path).symm ▸ wrong
  by_contra missing
  have noExec : (historyExecutions state.history).any (fun pair => pair.1.stage == stage) = false := by
    apply List.any_eq_false.mpr
    intro pair member equalStage
    rw [prefix_historyExecutions input C .uncapped accounting source seed truth tapes path] at member
    obtain ⟨execution,executed,rfl⟩ := List.mem_map.mp member
    exact missing ((mem_executedStages state.ledger stage).mpr ⟨execution,executed,beq_iff_eq.mp equalStage⟩)
  have empty := List.find?_eq_none.mp noPending stage (List.mem_finRange stage)
  rw [decide_eq_true reportedWrong,noExec] at empty
  exact empty rfl

theorem rule_at_good_terminal (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget limit) seed truth tapes n state)
    (active : state.halted = false) (cursor : state.cursor = I.stageCount)
    (matchable : Matchable I (ordinaryMismatches state.ledger)) :
    retainedRule input budget limit seed state.history = terminalMatchingAction I state.history ∧
      terminalMatchingAction I state.history ≠ .abandon := by
  obtain ⟨next,step,notAbandon⟩ := terminal_good_step input C hretained accounting budget limit seed truth tapes path active matchable
  have historyActive : historyHalted state.history = false :=
    (prefix_historyHalted input C .uncapped accounting (retainedRule input budget limit) seed truth tapes path).trans active
  have historyTerminal : historyCursor state.history = I.stageCount :=
    (prefix_historyCursor input C .uncapped accounting (retainedRule input budget limit) seed truth tapes path).trans cursor
  have raw := candidate_at_terminal input budget limit state.history historyActive historyTerminal
  have rawStep : Step input C .uncapped accounting tapes state
      ((fun (_ : Unit) history => retainedCandidate input budget limit history) seed state.history) next := by
    change Step input C .uncapped accounting tapes state (retainedCandidate input budget limit state.history) next
    rw [raw]
    exact step
  have pass := PRetRetainedGuard007.guarded_action_of_step input C hretained.1 accounting
    (fun (_ : Unit) history => retainedCandidate input budget limit history) seed truth tapes path rawStep
  exact ⟨pass.trans raw,notAbandon⟩

theorem stop_success (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) {Seed : Type*} (source : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C .uncapped accounting source seed truth tapes n state)
    (complete : allWritten state.ledger) (selected : terminalMatchingAction I state.history = .stop) :
    (stopState state false).ledger.success C := by
  classical
  have covers := terminal_stop_covers input C hretained.1 accounting source seed truth tapes path selected
  refine ⟨?_,rfl,?_,?_⟩
  · change decide (allWritten state.ledger) = true
    exact decide_eq_true complete
  · simp only [Ledger.windowObligations,hretained.2.1,hretained.2.2,reduceCtorEq,false_implies,implies_true,and_self]
  · intro stage
    change state.ledger.written stage = some (state.ledger.truth stage) ∨
      ∃ execution ∈ state.ledger.executions, execution.handle.stage = stage
    by_cases correct : state.ledger.written stage = some (state.ledger.truth stage)
    · exact Or.inl correct
    · have wrong : stage ∈ ordinaryMismatches state.ledger := by
        rw [mem_ordinaryMismatches]
        cases written : state.ledger.written stage with
        | none => exact (complete stage written).elim
        | some bit => cases ht : state.ledger.truth stage <;> cases bit <;> simp_all
      exact Or.inr ((mem_executedStages state.ledger stage).mp (covers wrong))

theorem halted_terminal_success (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget limit) seed truth tapes n state)
    (halted : state.halted = true) (cursor : state.cursor = I.stageCount) (complete : allWritten state.ledger)
    (matchable : Matchable I (ordinaryMismatches state.ledger)) : state.ledger.success C := by
  cases path with
  | initial => cases halted
  | @next n old next earlier step =>
    generalize action : retainedRule input budget limit seed old.history = chosen at step
    cases step <;> try cases halted
    case next.stop.refl =>
      have active : old.halted = false := by assumption
      have raw := (rule_at_good_terminal input C hretained accounting budget limit seed truth tapes earlier active cursor matchable).1
      exact stop_success input C hretained accounting (retainedRule input budget limit) seed truth tapes earlier complete
        (raw.symm.trans action)
    case next.abandon.refl =>
      have active : old.halted = false := by assumption
      obtain ⟨raw,notAbandon⟩ := rule_at_good_terminal input C hretained accounting budget limit seed truth tapes earlier active cursor matchable
      exact (notAbandon (raw.symm.trans action)).elim

end PRetCompletion
