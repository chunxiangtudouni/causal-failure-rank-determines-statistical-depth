module

public import PaperProofs.Retained.PRet_Alignment_Advance_004
public import PaperProofs.Retained.PRet_ScriptFrame_116

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics

namespace PRetAlignment

variable {I : Instance}

theorem prefix_replay_exists (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (retainedRule input budget limit) seed truth tapes n s) :
    ∃ cache, replayBudget I budget s.history s.cursor = some cache := by
  induction hp with
  | initial => exact ⟨⟨∅,budget/2⟩,rfl⟩
  | @next n s next earlier step ih =>
    obtain ⟨cache,replay⟩ := ih
    have frame := step_replayBudget_past input C hearly .uncapped accounting
      (retainedRule input budget limit) seed truth tapes earlier step budget
    have original := step
    generalize action : retainedRule input budget limit seed s.history = chosen at step
    cases step with
    | review | write | allocate | execute | stop | abandon => exact ⟨cache,frame.trans replay⟩
    | advance stage live written resources =>
      have historyActive : historyHalted s.history = false :=
        (prefix_historyHalted input C .uncapped accounting (retainedRule input budget limit)
          seed truth tapes earlier).trans live.1
      have historyCursor : historyCursor s.history = stage.val :=
        (prefix_historyCursor input C .uncapped accounting (retainedRule input budget limit)
          seed truth tapes earlier).trans live.2
      obtain ⟨old,error,oldReplay,healthy,valid,report,matchable⟩ :=
        rule_advance input budget limit seed s.history stage historyActive historyCursor action
      obtain ⟨child,childStep,_,_,_⟩ := replayStep_exists s.history old stage healthy valid error report matchable
      have reportFrame := step_reportedError_of_written input C hearly .uncapped accounting
        (retainedRule input budget limit) seed truth tapes earlier original stage rfl
      change reportedError (s.history ++ [.advanced stage]) stage = reportedError s.history stage at reportFrame
      refine ⟨child,?_⟩
      change replayBudget I budget _ (s.cursor+1) = some child
      rw [live.2, PRetBudgetReplay117.replayBudget_succ]
      change ((replayBudget I budget (s.history ++ [.advanced stage]) stage.val).bind
        (fun cache => replayBudgetStep I (s.history ++ [.advanced stage]) cache stage)) = some child
      have oldFrame : replayBudget I budget (s.history ++ [.advanced stage]) stage.val = some old := by
        rw [← live.2] at oldReplay ⊢
        exact frame.trans oldReplay
      rw [oldFrame]
      change replayBudgetStep I _ old stage = some child
      rw [PRetBudgetReplay117.replayStep_congr _ s.history old stage reportFrame]
      exact childStep

theorem referenceAlignment (input : StatisticalInput I) : ReferenceAlignment input := by
  intro C hretained accounting budget positive bound limit
  refine ⟨PRetScriptFrame116.terminalOnly input C accounting budget limit,?_⟩
  intro sample n stage _active cursor
  obtain ⟨_,_,hp⟩ := run_has_prefix input C .uncapped accounting (retainedRule input budget limit)
    (retainedRule_uncapped_legal input C hretained accounting budget limit) sample n
  obtain ⟨cache,replay⟩ := prefix_replay_exists input C hretained.1 accounting budget limit sample.1 _ _ hp
  rw [cursor] at replay
  have initialValid : ReferenceBudgetValid (budget/2) := by constructor <;> linarith
  obtain ⟨healthy,valid,errors⟩ := replayBudget_sound budget _ initialValid stage.val (Nat.le_of_lt stage.isLt) cache replay
  refine ⟨cache,replay,healthy,valid,?_⟩
  rw [errors, PRetActualReportedErrors048.prefix_reportedErrors input C hretained.1 .uncapped accounting
    (retainedRule input budget limit) sample.1 _ _ hp stage.val]

end PRetAlignment
