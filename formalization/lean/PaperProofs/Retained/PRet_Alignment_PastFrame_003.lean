module

public import PaperProofs.Retained.PRet_Alignment_ReplaySound_002
public import PaperProofs.Retained.PRet_ActualReportedErrors_048

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics

namespace PRetAlignment

variable {I : Instance} {Seed : Type*}

theorem step_written_past (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (step : Step input C mode accounting tapes s action next)
    (stage : I.Stage) (past : stage.val < s.cursor) : next.ledger.written stage = s.ledger.written stage := by
  classical
  cases step with
  | write current bit live port resources =>
    have ne : stage ≠ current := by
      intro eq
      subst stage
      exact (Nat.lt_irrefl _ (live.2 ▸ past))
    change (reportedWriteLedger C s current bit).written stage = s.ledger.written stage
    simp only [reportedWriteLedger]
    split_ifs <;> simp only [writeLedger, Function.update_of_ne ne]
  | review | allocate | execute | advance => rfl
  | stop | abandon => simp only [stopState]

theorem step_reportedError_of_written (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s next : State I} (hp : Prefix input C mode accounting source seed truth tapes n s)
    (step : Step input C mode accounting tapes s (source seed s.history) next)
    (stage : I.Stage) (written : next.ledger.written stage = s.ledger.written stage) :
    reportedError next.history stage = reportedError s.history stage := by
  rw [PRetActualReportedErrors048.prefix_reportedError input C hearly mode accounting source seed truth tapes (.next hp step) stage,
    PRetActualReportedErrors048.prefix_reportedError input C hearly mode accounting source seed truth tapes hp stage,
    step_truth_unchanged input C mode accounting tapes step, written]

theorem step_replayBudget_past (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s next : State I} (hp : Prefix input C mode accounting source seed truth tapes n s)
    (step : Step input C mode accounting tapes s (source seed s.history) next)
    (budget : ℚ) : replayBudget I budget next.history s.cursor = replayBudget I budget s.history s.cursor := by
  apply PRetBudgetReplay117.replayBudget_congr
  intro stage past
  exact step_reportedError_of_written input C hearly mode accounting source seed truth tapes hp step stage
    (step_written_past input C mode accounting tapes step stage past)

end PRetAlignment
