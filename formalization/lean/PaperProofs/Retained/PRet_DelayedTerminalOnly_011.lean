module

public import PaperProofs.Retained.PRet_DelayedPolicy_010

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetDelayedTerminalOnly011

open Common Common.Native PRetDelayedPolicy010

variable {I : Instance}

private theorem reportedWrite_frames (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s stage bit).commitments = s.ledger.commitments ∧
      (reportedWriteLedger C s stage bit).executions = s.ledger.executions := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem terminalOnly_of_barrier_actions {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hbarrier : ∀ seed history, isCorrection (policy seed history) = true → historyCursor history = I.stageCount) :
    TerminalOnly input C mode accounting policy := by
  intro seed truth tapes n state hp
  induction hp with
  | initial => intro _; exact ⟨rfl, rfl⟩
  | @next n s s' hp step ih =>
    intro hcursor
    generalize haction : policy seed s.history = action at step
    cases step with
    | review => exact ih hcursor
    | write stage bit _ _ _ =>
      have hi := ih hcursor
      have hf := reportedWrite_frames C s stage bit
      exact ⟨hf.1.trans hi.1, hf.2.trans hi.2⟩
    | allocate handle tool _ _ _ _ _ _ _ =>
      have hb := hbarrier seed s.history (by simp only [haction, isCorrection])
      rw [prefix_historyCursor input C mode accounting policy seed truth tapes hp] at hb
      change s.cursor < I.stageCount at hcursor
      omega
    | execute handle tool _ _ _ _ _ _ _ _ =>
      have hb := hbarrier seed s.history (by simp only [haction, isCorrection])
      rw [prefix_historyCursor input C mode accounting policy seed truth tapes hp] at hb
      change s.cursor < I.stageCount at hcursor
      omega
    | advance =>
      apply ih
      change s.cursor + 1 < I.stageCount at hcursor
      omega
    | stop => exact ih hcursor
    | abandon => exact ih hcursor

/-- The same-Seed delayed policy constructed from the original source
history rule makes no actual commitment or execution before the barrier.
This is proved from every actual Prefix, not supplied as a policy field. -/
theorem delayed_terminalOnly {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (sourceRule : PolicyRule I Seed) :
    TerminalOnly input C .uncapped accounting (PRetDelayedPolicy010.rule accounting sourceRule) :=
  terminalOnly_of_barrier_actions input C .uncapped accounting _ (rule_correction accounting sourceRule)

end PaperProofs.Retained.PRetDelayedTerminalOnly011
