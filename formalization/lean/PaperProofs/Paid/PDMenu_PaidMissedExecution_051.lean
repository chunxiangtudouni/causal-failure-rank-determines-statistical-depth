module

public import PaperProofs.Common.NativeBellmanLower

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

private theorem reportedWrite_execution_list (C : Contract I) (state : State I) (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C state stage bit).executions = state.ledger.executions := by
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

/-- Under the original current-payment execution window, an old stage
cannot receive a new execution after the cursor has passed it. -/
theorem paidRun_unexecuted_behind_cursor (input : StatisticalInput I) (C : Contract I)
    (hcurrent : C.execution = .currentWindow) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (start extra : ℕ) (head : I.Stage)
    (hold : head.val < (run input C mode accounting rule sample start).cursor)
    (hno : ∀ e ∈ (run input C mode accounting rule sample start).ledger.executions, e.handle.stage ≠ head) :
    ∀ e ∈ (run input C mode accounting rule sample (start + extra)).ledger.executions, e.handle.stage ≠ head := by
  induction extra with
  | zero => exact hno
  | succ extra ih =>
    by_cases hh : (run input C mode accounting rule sample (start + extra)).halted = true
    · rw [Nat.add_succ, run_succ_of_halted input C mode accounting rule sample (start + extra) hh]
      exact ih
    · have ha : (run input C mode accounting rule sample (start + extra)).halted = false := Bool.eq_false_iff.mpr hh
      obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample (start + extra)
      obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hp ha
      rw [Nat.add_succ, run_succ_of_step input C mode accounting rule sample (start + extra) next ha hs]
      have hc := run_cursor_monotone input C mode accounting rule hlegal sample (Nat.le_add_right start extra)
      change (run input C mode accounting rule sample start).cursor ≤
        (run input C mode accounting rule sample (start + extra)).cursor at hc
      generalize rule sample.1 (run input C mode accounting rule sample (start + extra)).history = action at hs
      cases hs with
      | execute handle tool active valid compatible committed unused uncorrected window resources =>
        intro e hem
        change e ∈ (run input C mode accounting rule sample (start + extra)).ledger.executions ++
          [⟨handle, tool, (run input C mode accounting rule sample (start + extra)).clock⟩] at hem
        rcases List.mem_append.mp hem with hbefore | hnew
        · exact ih e hbefore
        · obtain rfl := List.mem_singleton.mp hnew
          intro he
          have hw := window hcurrent
          rw [he] at hw
          omega
      | write current bit live port resources =>
        intro e hem
        exact ih e (by simpa only [record, reportedWrite_execution_list] using hem)
      | review | allocate | advance | stop | abandon => exact ih

/-- Passing a wrong, physically unexecuted head creates permanent original
failure, even if the head already owns an allocated commitment. -/
theorem paidWrong_unexecuted_behind_cursor_failure (input : StatisticalInput I) (C : Contract I)
    (hcurrent : C.execution = .currentWindow) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (start : ℕ) (head : I.Stage)
    (hold : head.val < (run input C mode accounting rule sample start).cursor)
    (hwrong : (run input C mode accounting rule sample start).ledger.written head =
      some (!(run input C mode accounting rule sample start).ledger.truth head))
    (hno : ∀ e ∈ (run input C mode accounting rule sample start).ledger.executions, e.handle.stage ≠ head) :
    ¬runSuccess input C mode accounting rule sample := by
  rintro ⟨stopped, hhalt, hsuccess⟩
  let now := max start stopped
  obtain ⟨delta, hnowStop⟩ := Nat.exists_eq_add_of_le (Nat.le_max_right start stopped)
  have hstate : run input C mode accounting rule sample now = run input C mode accounting rule sample stopped := by
    change run input C mode accounting rule sample (max start stopped) = _
    rw [hnowStop, run_after_halt input C mode accounting rule sample stopped hhalt delta]
  have hsuccessNow : (run input C mode accounting rule sample now).ledger.success C := by rw [hstate]; exact hsuccess
  obtain ⟨extra, hnowStart⟩ := Nat.exists_eq_add_of_le (Nat.le_max_left start stopped)
  have hwriteNow := run_written_behind_cursor input C mode accounting rule hlegal sample start extra head hold
  have hnoNow := paidRun_unexecuted_behind_cursor input C hcurrent mode accounting rule hlegal sample start extra head hold hno
  change max start stopped = start + extra at hnowStart
  rw [← hnowStart] at hwriteNow hnoNow
  have htruth : (run input C mode accounting rule sample now).ledger.truth head =
      (run input C mode accounting rule sample start).ledger.truth head := by
    rw [run_truth input C mode accounting rule hlegal sample now, run_truth input C mode accounting rule hlegal sample start]
  rcases hsuccessNow.2.2.2 head with hright | ⟨e, he, hes⟩
  · rw [hwriteNow, hwrong, htruth] at hright
    cases ht : (run input C mode accounting rule sample start).ledger.truth head <;>
      simp only [ht, Bool.not_true, Bool.not_false] at hright
    all_goals cases hright
  · exact hnoNow e he hes

end PDMenu
