module

public import PaperProofs.Retained.PRet_Completion_Selection_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics

namespace PRetCompletion

variable {I : Instance}

theorem reportedErrors_congr (left right : List (VisibleEvent I)) (next : ℕ)
    (reports : ∀ stage, reportedError left stage = reportedError right stage) :
    reportedErrors I left next = reportedErrors I right next := by
  ext stage
  simp only [reportedErrors,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [reports stage]

def AssignmentChoices (state : State I) : Prop :=
  ∀ allocation ∈ state.ledger.commitments, ∀ assignment,
    firstAssignment I (reportedErrors I state.history I.stageCount) = some assignment →
      assignment[allocation.handle.stage.val]?.join = some allocation.tool

set_option backward.isDefEq.respectTransparency.types false in
theorem prefix_assignmentChoices (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget limit) seed truth tapes n state) :
    AssignmentChoices state := by
  classical
  induction path with
  | initial => intro allocation member; cases member
  | @next n state next earlier step ih =>
    have original := step
    have frame (written : next.ledger.written = state.ledger.written) :
        reportedErrors I next.history I.stageCount = reportedErrors I state.history I.stageCount := by
      apply reportedErrors_congr
      intro stage
      exact PRetAlignment.step_reportedError_of_written input C hearly .uncapped accounting
        (retainedRule input budget limit) seed truth tapes earlier original stage (congrFun written stage)
    generalize haction : retainedRule input budget limit seed state.history = action at step
    cases step with
    | review stage live port resources =>
      have before : state.cursor < I.stageCount := live.2 ▸ stage.isLt
      have empty := (PRetScriptFrame116.prefix_no_corrections input C .uncapped accounting budget limit
        seed truth tapes earlier before).1
      intro allocation member
      change allocation ∈ state.ledger.commitments at member
      rw [empty] at member
      cases member
    | write stage bit live port resources =>
      have before : state.cursor < I.stageCount := live.2 ▸ stage.isLt
      have empty := (PRetScriptFrame116.prefix_no_corrections input C .uncapped accounting budget limit
        seed truth tapes earlier before).1
      have newEmpty : (reportedWriteLedger C state stage bit).commitments = [] := by
        simp only [reportedWriteLedger]
        split_ifs
        exact empty
      intro allocation member
      change allocation ∈ (reportedWriteLedger C state stage bit).commitments at member
      rw [newEmpty] at member
      cases member
    | advance stage live written resources =>
      have before : state.cursor < I.stageCount := live.2 ▸ stage.isLt
      have empty := (PRetScriptFrame116.prefix_no_corrections input C .uncapped accounting budget limit
        seed truth tapes earlier before).1
      intro allocation member
      change allocation ∈ state.ledger.commitments at member
      rw [empty] at member
      cases member
    | allocate handle tool active valid compatible unused unallocated window resources =>
      have bound := (prefix_cursorInvariant input C .uncapped accounting (retainedRule input budget limit)
        seed truth tapes earlier).bound
      have terminal : state.cursor = I.stageCount := by
        by_contra unequal
        have before : state.cursor < I.stageCount := by omega
        have hc : historyCursor state.history < I.stageCount := by
          rw [prefix_historyCursor input C .uncapped accounting (retainedRule input budget limit) seed truth tapes earlier]
          exact before
        exact (PRetScriptFrame116.rule_no_correction input budget limit seed state.history hc handle tool).1 haction
      have historyActive : historyHalted state.history = false :=
        (prefix_historyHalted input C .uncapped accounting (retainedRule input budget limit) seed truth tapes earlier).trans active
      have historyTerminal : historyCursor state.history = I.stageCount :=
        (prefix_historyCursor input C .uncapped accounting (retainedRule input budget limit) seed truth tapes earlier).trans terminal
      have raw := rule_raw_of_ne_abandon input budget limit seed state.history (.allocate handle tool) (by intro impossible; cases impossible) haction
      have terminalAction := (candidate_at_terminal input budget limit state.history historyActive historyTerminal).symm.trans raw
      obtain ⟨assignment,stage,first,_pending,slot,_visible,_noCommit,hstage⟩ :=
        terminal_allocate_selection state.history handle tool terminalAction
      intro allocation member chosen query
      rw [frame rfl] at query
      have same : chosen = assignment := Option.some.inj (query.symm.trans first)
      subst chosen
      change allocation ∈ state.ledger.commitments ++ [⟨handle,tool,state.clock⟩] at member
      rcases List.mem_append.mp member with old | fresh
      · exact ih allocation old assignment first
      · have eq : allocation = ⟨handle,tool,state.clock⟩ := List.mem_singleton.mp fresh
        subst allocation
        change assignment[handle.stage.val]?.join = some tool
        rw [hstage]
        exact slot
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      intro allocation member assignment query
      rw [frame rfl] at query
      exact ih allocation member assignment query
    | stop active =>
      intro allocation member assignment query
      rw [frame rfl] at query
      exact ih allocation member assignment query
    | abandon active =>
      intro allocation member assignment query
      rw [frame rfl] at query
      exact ih allocation member assignment query

end PRetCompletion
