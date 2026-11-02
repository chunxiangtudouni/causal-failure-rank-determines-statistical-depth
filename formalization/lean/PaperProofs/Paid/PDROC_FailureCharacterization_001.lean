module

public import PaperProofs.Paid.PDROC_TruthfulContinuation_001
public import PaperProofs.Paid.PDROC_FirstFailure_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem existingCorrect_of_noPast_current (s : State I) (hcu : CursorInvariant s)
    (hpast : ∀ stage : I.Stage, ¬ PastUnrepairedError s stage)
    (hcurrent : ∀ stage : I.Stage, stage.val = s.cursor → s.ledger.written stage ≠ none →
      s.ledger.written stage = some (s.ledger.truth stage) ∨
        ∃ e ∈ s.ledger.executions, e.handle.stage = stage) : ExistingPhysicallyCorrect s := by
  intro stage hw
  rcases lt_trichotomy stage.val s.cursor with hlt | heq | hgt
  · by_cases hex : ∃ e ∈ s.ledger.executions, e.handle.stage = stage
    · exact Or.inr hex
    · left
      cases hb : s.ledger.written stage with
      | none => exact (hw hb).elim
      | some bit =>
        have hbits : bit = s.ledger.truth stage ∨ bit = !s.ledger.truth stage := by
          cases bit <;> cases s.ledger.truth stage <;> decide
        rcases hbits with hcorrect | hwrong
        · exact congrArg some hcorrect
        · exact (hpast stage ⟨hlt, hb.trans (congrArg some hwrong),
            fun e he hs => hex ⟨e, he, hs⟩⟩).elim
  · exact hcurrent stage heq hw
  · exact (hw (hcu.future_written stage hgt)).elim

/-- For every actual prefix, if no past physical error was missed and every
already written current output is physically correct, a genuine successful
uncapped continuation exists. No detector assumption is hidden in a Policy. -/
theorem prefix_not_permanentlyFailed_of_noPast_current (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (world : input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed (input.truthAt world) (worldTapes input world) n s)
    (ha : s.halted = false) (hpast : ∀ stage : I.Stage, ¬ PastUnrepairedError s stage)
    (hcurrent : ∀ stage : I.Stage, stage.val = s.cursor → s.ledger.written stage ≠ none →
      s.ledger.written stage = some (s.ledger.truth stage) ∨
        ∃ e ∈ s.ledger.executions, e.handle.stage = stage) :
    ¬ PermanentlyFailed input C accounting world s := by
  have hcu := prefix_cursorInvariant input C mode accounting rule seed _ _ hp
  exact not_not_intro (truthfulContinuation_exists input C accounting (worldTapes input world) s
    (prefix_invariant input C mode accounting rule seed _ _ hp)
    (prefix_deadlineInvariant input C mode accounting rule seed _ _ hp)
    hcu ha (prefix_pastPortsWritten input C mode accounting rule seed _ _ hp)
    (existingCorrect_of_noPast_current s hcu hpast hcurrent))

end PDROC
