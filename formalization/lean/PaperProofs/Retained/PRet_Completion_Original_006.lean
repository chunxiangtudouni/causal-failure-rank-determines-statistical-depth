module

public import PaperProofs.Retained.PRet_Completion_Halt_005
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics

namespace PRetCompletion

variable {I : Instance}

theorem terminalScriptCompletion (input : StatisticalInput I) : TerminalScriptCompletion input := by
  intro C hretained accounting budget limit sample start
  dsimp only
  intro _active cursor complete matchable
  have legal := retainedRule_uncapped_legal input C hretained accounting budget limit
  obtain ⟨later,bound,halted⟩ := run_halts_after_allWritten input C .uncapped accounting
    (retainedRule input budget limit) legal sample start complete
  have writtenEq : (run input C .uncapped accounting (retainedRule input budget limit) sample later).ledger.written =
      (run input C .uncapped accounting (retainedRule input budget limit) sample start).ledger.written := by
    funext stage
    cases written : (run input C .uncapped accounting (retainedRule input budget limit) sample start).ledger.written stage with
    | none => exact (complete stage written).elim
    | some bit =>
      have still := run_written_some_after input C .uncapped accounting (retainedRule input budget limit)
        legal sample start (later-start) stage bit written
      rw [Nat.add_sub_of_le bound] at still
      exact still
  have truthEq : (run input C .uncapped accounting (retainedRule input budget limit) sample later).ledger.truth =
      (run input C .uncapped accounting (retainedRule input budget limit) sample start).ledger.truth :=
    (run_truth input C .uncapped accounting (retainedRule input budget limit) legal sample later).trans
      (run_truth input C .uncapped accounting (retainedRule input budget limit) legal sample start).symm
  have errorsEq : ordinaryMismatches (run input C .uncapped accounting (retainedRule input budget limit) sample later).ledger =
      ordinaryMismatches (run input C .uncapped accounting (retainedRule input budget limit) sample start).ledger := by
    simp only [ordinaryMismatches,writtenEq,truthEq]
  have completeLater : allWritten (run input C .uncapped accounting (retainedRule input budget limit) sample later).ledger := by
    simpa only [allWritten,writtenEq] using complete
  have cursorLater : (run input C .uncapped accounting (retainedRule input budget limit) sample later).cursor = I.stageCount := by
    have lower := run_cursor_monotone input C .uncapped accounting (retainedRule input budget limit) legal sample bound
    change (run input C .uncapped accounting (retainedRule input budget limit) sample start).cursor ≤
      (run input C .uncapped accounting (retainedRule input budget limit) sample later).cursor at lower
    have upper := (run_cursorInvariant input C .uncapped accounting (retainedRule input budget limit) legal sample later).bound
    rw [cursor] at lower
    exact Nat.le_antisymm upper lower
  obtain ⟨_,_,path⟩ := run_has_prefix input C .uncapped accounting (retainedRule input budget limit) legal sample later
  have success := halted_terminal_success input C hretained accounting budget limit sample.1 _ _ path
    halted cursorLater completeLater (errorsEq.symm ▸ matchable)
  have well := prefix_ledgerWellFormed input C .uncapped accounting (retainedRule input budget limit) sample.1 _ _ path
  have executed := executedStages_eq_mismatches_of_success _ C well success
  have count : (executedStages (run input C .uncapped accounting (retainedRule input budget limit) sample later).ledger).card =
      (run input C .uncapped accounting (retainedRule input budget limit) sample later).ledger.executions.length := by
    rw [executedStages,List.toFinset_card_of_nodup well.execution_stages,List.length_map]
  exact ⟨later,bound,halted,success,count.symm.trans ((congrArg Finset.card executed).trans (congrArg Finset.card errorsEq))⟩

end PRetCompletion
