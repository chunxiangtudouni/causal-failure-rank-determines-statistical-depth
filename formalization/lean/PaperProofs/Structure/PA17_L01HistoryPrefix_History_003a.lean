module

public import PaperProofs.Common.CompactPriceClaims
public import PaperProofs.Common.NativeCausality
public import PaperProofs.Common.NativeHistoryReplay

/-! Actual native histories extend causally. Under original early reporting,
completed-stage declarations never change at later clocks. This does not
assert that arbitrary legal policies admit compact error commands. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Common.Native.PA17L01HistoryPrefixHistory003

variable {I : Instance} {Seed : Type*}

theorem step_history_prefix (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {before after : State I} {action : Action I}
    (step : Step input C mode accounting tapes before action after) :
    before.history.IsPrefix after.history := by
  cases step <;> exact ⟨_, rfl⟩

theorem step_completed_fields (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (tapes : ReviewTapes input) {before after : State I} {action : Action I}
    (step : Step input C mode accounting tapes before action after)
    (stage : I.Stage) (hpast : stage.val < before.cursor) :
    historyWrite after.history stage = historyWrite before.history stage ∧
      historyReport after.history stage = historyReport before.history stage := by
  classical
  cases step with
  | write current bit live port resources =>
    have hne : current ≠ stage := by
      intro heq
      subst current
      have hcursor := live.2
      omega
    simp [record, historyWrite, historyReport, writeResponses, hearly,
      List.filterMap_append, eventWrite, eventReport, hne]
  | review | allocate | execute | advance | stop | abandon =>
    simp [record, stopState, historyWrite, historyReport, List.filterMap_append,
      eventWrite, eventReport]

theorem step_completed_declaration (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (tapes : ReviewTapes input) {before after : State I} {action : Action I}
    (step : Step input C mode accounting tapes before action after)
    (stage : I.Stage) (hpast : stage.val < before.cursor) :
    CompactPrice.declaration after.history stage = CompactPrice.declaration before.history stage := by
  have fields := step_completed_fields input C hearly mode accounting tapes step stage hpast
  unfold CompactPrice.declaration
  rw [fields.1, fields.2]

theorem run_history_step_prefix (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (legal : LegalRule input C mode accounting rule) (sample : Seed × input.World) (clock : Nat) :
    (run input C mode accounting rule sample clock).history.IsPrefix
      (run input C mode accounting rule sample (clock + 1)).history := by
  by_cases hh : (run input C mode accounting rule sample clock).halted = true
  · rw [run_succ_of_halted input C mode accounting rule sample clock hh]
  · have ha := Bool.eq_false_iff.mpr hh
    obtain ⟨n, _, hp⟩ := run_has_prefix input C mode accounting rule legal sample clock
    obtain ⟨next, step⟩ := legal sample.1 _ _ n _ hp ha
    rw [run_succ_of_step input C mode accounting rule sample clock next ha step]
    exact step_history_prefix input C mode accounting _ step

theorem run_history_prefix (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (legal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    {earlier later : Nat} (hle : earlier ≤ later) :
    (run input C mode accounting rule sample earlier).history.IsPrefix
      (run input C mode accounting rule sample later).history := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction extra with
  | zero => simp
  | succ extra ih =>
    exact ih.trans (run_history_step_prefix input C mode accounting rule legal sample (earlier + extra))

theorem run_completed_declaration (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (legal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) {earlier later : Nat} (hle : earlier ≤ later)
    (stage : I.Stage) (hpast : stage.val < (run input C mode accounting rule sample earlier).cursor) :
    CompactPrice.declaration (run input C mode accounting rule sample later).history stage =
      CompactPrice.declaration (run input C mode accounting rule sample earlier).history stage := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction extra with
  | zero => simp
  | succ extra ih =>
    let clock := earlier + extra
    change CompactPrice.declaration (run input C mode accounting rule sample (clock + 1)).history stage = _
    by_cases hh : (run input C mode accounting rule sample clock).halted = true
    · rw [run_succ_of_halted input C mode accounting rule sample clock hh]
      exact ih
    · have ha := Bool.eq_false_iff.mpr hh
      obtain ⟨n, _, hp⟩ := run_has_prefix input C mode accounting rule legal sample clock
      obtain ⟨next, step⟩ := legal sample.1 _ _ n _ hp ha
      rw [run_succ_of_step input C mode accounting rule sample clock next ha step]
      apply (step_completed_declaration input C hearly mode accounting _ step stage ?_).trans ih
      exact hpast.trans_le (run_cursor_monotone input C mode accounting rule legal sample (Nat.le_add_right earlier extra))

end PaperProofs.Common.Native.PA17L01HistoryPrefixHistory003
