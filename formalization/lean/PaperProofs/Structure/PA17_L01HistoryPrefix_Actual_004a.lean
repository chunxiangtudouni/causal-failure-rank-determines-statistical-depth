module

public import PaperProofs.Structure.PA17_L01HistoryPrefix_Commands_001a
public import PaperProofs.Structure.PA17_L01HistoryPrefix_History_003a

/-! Actual commandsAt histories are prefixes along every legal early-reporting
run. Cursor bounds/monotonicity and past-declaration stability come from
existing actual Native proofs, with no new induction or history eligibility. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Common.Native.PA17L01HistoryPrefixActual004

open PaperProofs.Structure.LaminarTree

variable {I : Instance} {Seed : Type*}

theorem run_history_cursor (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (legal : LegalRule input C mode accounting rule) (sample : Seed × input.World) (clock : Nat) :
    historyCursor (run input C mode accounting rule sample clock).history =
      (run input C mode accounting rule sample clock).cursor := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C mode accounting rule legal sample clock
  exact prefix_historyCursor input C mode accounting rule sample.1 _ _ hp

theorem run_commands_prefix (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (legal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) {earlier later : Nat} (hle : earlier ≤ later) :
    (CompactPrice.commandsAt I (run input C mode accounting rule sample earlier).history).IsPrefix
      (CompactPrice.commandsAt I (run input C mode accounting rule sample later).history) := by
  apply PA17L01HistoryPrefixCommands001.commandsAt_prefix
  · rw [run_history_cursor input C mode accounting rule legal sample later]
    exact (run_cursorInvariant input C mode accounting rule legal sample later).bound
  · rw [run_history_cursor input C mode accounting rule legal sample earlier,
      run_history_cursor input C mode accounting rule legal sample later]
    exact run_cursor_monotone input C mode accounting rule legal sample hle
  · intro stage hpast
    apply (PA17L01HistoryPrefixHistory003.run_completed_declaration input C hearly mode accounting
      rule legal sample hle stage ?_).symm
    rw [← run_history_cursor input C mode accounting rule legal sample earlier]
    exact hpast

theorem policy_commands_prefix [MeasurableSpace Seed] (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (sample : Seed × input.World)
    {earlier later : Nat} (hle : earlier ≤ later) :
    (CompactPrice.commandsAt I (run input C mode accounting policy.rule sample earlier).history).IsPrefix
      (CompactPrice.commandsAt I (run input C mode accounting policy.rule sample later).history) := by
  exact run_commands_prefix input C hearly mode accounting policy.rule policy.legal sample hle

end PaperProofs.Common.Native.PA17L01HistoryPrefixActual004
