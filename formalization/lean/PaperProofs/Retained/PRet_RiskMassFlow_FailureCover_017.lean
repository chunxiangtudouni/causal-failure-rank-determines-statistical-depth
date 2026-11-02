module

public import PaperProofs.Retained.PRet_RiskMassFlow_StateFacts_016

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory
open scoped ENNReal

namespace PRetRiskMassFlow

variable {I : Instance}

theorem prefix_stop_success (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (_positive : 0 < budget) (_small : budget ≤ 1/2)
    (sample : Unit × input.World) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n state)
    (active : state.halted = false) (selected : retainedRule input budget none sample.1 state.history = .stop) :
    (stopState state false).ledger.success C := by
  have historyActive : historyHalted state.history = false :=
    (prefix_historyHalted input C .uncapped accounting (retainedRule input budget none) sample.1 _ _ path).trans active
  have raw := PRetCompletion.rule_raw_of_ne_abandon input budget none sample.1 state.history .stop
    (by intro impossible; cases impossible) selected
  have notBefore : ¬state.cursor < I.stageCount := by
    intro before
    have historyBefore : historyCursor state.history < I.stageCount := by
      rw [prefix_historyCursor input C .uncapped accounting (retainedRule input budget none) sample.1 _ _ path]
      exact before
    exact candidate_before_not_stop input budget state.history historyActive historyBefore raw
  have terminal : state.cursor = I.stageCount :=
    Nat.le_antisymm (prefix_cursorInvariant input C .uncapped accounting (retainedRule input budget none) sample.1 _ _ path).bound
      (Nat.le_of_not_lt notBefore)
  have historyTerminal : historyCursor state.history = I.stageCount :=
    (prefix_historyCursor input C .uncapped accounting (retainedRule input budget none) sample.1 _ _ path).trans terminal
  have actualTerminal := (PRetCompletion.candidate_at_terminal input budget none state.history historyActive historyTerminal).symm.trans raw
  exact PRetCompletion.stop_success input C hretained accounting (retainedRule input budget none) sample.1 _ _ path
    (prefix_allWritten_at_terminal input C accounting budget sample.1 _ _ path terminal) actualTerminal

set_option backward.isDefEq.respectTransparency.types false in
theorem prefix_abandon_fatal (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (sample : Unit × input.World) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n state)
    (active : state.halted = false) (selected : retainedRule input budget none sample.1 state.history = .abandon) :
    ∃ stage,sample ∈ fatal input C accounting budget stage := by
  classical
  by_cases before : state.cursor < I.stageCount
  · let stage : I.Stage := ⟨state.cursor,before⟩
    have cursor : state.cursor = stage.val := rfl
    cases written : state.ledger.written stage with
    | none =>
      exact ((prefix_rule_ne_abandon_on_open input C hretained.1 accounting budget positive small sample.1 _ _
        path active stage cursor written).2 selected).elim
    | some bit =>
      obtain ⟨cache,replay,healthy,valid,_errors⟩ :=
        prefix_cache_at_cursor input C hretained.1 accounting budget positive small sample.1 _ _ path
      rw [cursor] at replay healthy
      let error : Bool := bit != state.ledger.truth stage
      have report : reportedError state.history stage = some error := by
        rw [PRetActualReportedErrors048.prefix_reportedError input C hretained.1 .uncapped accounting
          (retainedRule input budget none) sample.1 _ _ path stage,written]
        rfl
      have historyWritten : historyWrite state.history stage = some (bit,state.ledger.writeSerial stage) := by
        rw [prefix_historyWrite input C .uncapped accounting (retainedRule input budget none) sample.1 _ _ path stage,written]
        rfl
      have historyActive : historyHalted state.history = false :=
        (prefix_historyHalted input C .uncapped accounting (retainedRule input budget none) sample.1 _ _ path).trans active
      have historyCursor : historyCursor state.history = stage.val :=
        (prefix_historyCursor input C .uncapped accounting (retainedRule input budget none) sample.1 _ _ path).trans cursor
      have obstructed : ¬Matchable I (if error then insert stage cache.errors else cache.errors) := by
        intro matchable
        have candidate := candidate_at_reported input budget state.history stage cache historyActive historyCursor
          replay healthy valid (bit,state.ledger.writeSerial stage) historyWritten error report
        rw [ite_eq_left matchable] at candidate
        have rawStep : Step input C .uncapped accounting (worldTapes input sample.2) state
            (retainedCandidate input budget none state.history)
            (record accounting state (.advance stage) [.advanced stage] (advanceLedger state stage) (state.cursor+1) false) := by
          rw [candidate]
          exact Step.advance state stage ⟨active,cursor⟩ (by rw [written]; exact Option.some_ne_none _) (Or.inl rfl)
        have pass := PRetRetainedGuard007.guarded_action_of_step input C hretained.1 accounting
          (fun (_ : Unit) history => retainedCandidate input budget none history) sample.1 _ _ path rawStep
        have advance : retainedRule input budget none sample.1 state.history = .advance stage := pass.trans candidate
        rw [advance] at selected
        cases selected
      have errorTrue : error = true := by
        by_contra notTrue
        have falseError := Bool.eq_false_iff.mpr notTrue
        rw [falseError] at obstructed
        exact obstructed healthy.2.2
      have badChild : ¬Matchable I (insert stage cache.errors) := by
        simpa only [errorTrue,↓reduceIte] using obstructed
      have noTool := (rankCase_noTool_iff stage cache.errors healthy).mpr badChild
      obtain ⟨history,entered,replayEq,_progress⟩ :=
        prefix_testing_origin input C hretained accounting budget positive small sample path active stage cursor
      have entryReplay : replayBudget I budget history stage.val = some cache := replayEq.trans replay
      have entryKindEq : entryKind I budget stage history = some .noTool := by
        unfold entryKind
        rw [entryReplay]
        exact noTool
      have wrong := prefix_reported_true_wrong input C hretained.1 accounting budget sample path stage (errorTrue ▸ report)
      refine ⟨stage,?_⟩
      change sample ∈ writeError input C accounting budget stage ∧
        (entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample).bind
          (entryKind I budget stage) = some .noTool
      refine ⟨⟨n,?_⟩,?_⟩
      · change (run input C .uncapped accounting (retainedRule input budget none) sample n).ledger.written stage =
          some (!(run input C .uncapped accounting (retainedRule input budget none) sample n).ledger.truth stage)
        rw [prefix_eq_run_sample input C accounting budget sample path]
        exact wrong
      · rw [entered]
        exact entryKindEq
  · have terminal : state.cursor = I.stageCount :=
      Nat.le_antisymm (prefix_cursorInvariant input C .uncapped accounting (retainedRule input budget none) sample.1 _ _ path).bound
        (Nat.le_of_not_lt before)
    have matchable := prefix_matchable_at_terminal input C hretained.1 accounting budget positive small sample.1 _ _ path terminal
    obtain ⟨raw,notAbandon⟩ := PRetCompletion.rule_at_good_terminal input C hretained accounting budget none sample.1 _ _ path active terminal matchable
    exact (notAbandon (raw.symm.trans selected)).elim

theorem prefix_halted_success_or_fatal (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (sample : Unit × input.World) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n state) (halted : state.halted = true) :
    state.ledger.success C ∨ ∃ stage,sample ∈ fatal input C accounting budget stage := by
  cases path with
  | initial => cases halted
  | @next n state next earlier step =>
    generalize action : retainedRule input budget none sample.1 state.history = selected at step
    cases step <;> try cases halted
    case next.stop.refl =>
      have active : state.halted = false := by assumption
      exact Or.inl (prefix_stop_success input C hretained accounting budget positive small sample earlier active action)
    case next.abandon.refl =>
      have active : state.halted = false := by assumption
      exact Or.inr (prefix_abandon_fatal input C hretained accounting budget positive small sample earlier active action)

theorem failure_subset_nontermination_union_fatal (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2) :
    {sample : Unit × input.World | ¬runSuccess input C .uncapped accounting (retainedRule input budget none) sample} ⊆
      {sample : Unit × input.World | ¬∃ n,(run input C .uncapped accounting (retainedRule input budget none) sample n).halted = true} ∪
        ⋃ stage : I.Stage,fatal input C accounting budget stage := by
  intro sample failed
  by_cases halted : ∃ n,(run input C .uncapped accounting (retainedRule input budget none) sample n).halted = true
  · obtain ⟨n,halted⟩ := halted
    obtain ⟨_,_,path⟩ := run_has_prefix input C .uncapped accounting (retainedRule input budget none)
      (retainedRule_uncapped_legal input C hretained accounting budget none) sample n
    rcases prefix_halted_success_or_fatal input C hretained accounting budget positive small sample path halted with success | ⟨stage,fatal⟩
    · exact (failed ⟨n,halted,success⟩).elim
    · exact Or.inr (Set.mem_iUnion.mpr ⟨stage,fatal⟩)
  · exact Or.inl halted

end PRetRiskMassFlow
