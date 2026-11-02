module

public import PaperProofs.Paid.PDMenu_MenuAdvanceRun_098

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

theorem menu_run_allocate (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (sample : Seed × input.World)
    (clock : ℕ) (handle : MismatchHandle I) (tool : I.Tool)
    (hactive : (run input C .uncapped accounting rule sample clock).halted = false)
    (haction : rule sample.1 (run input C .uncapped accounting rule sample clock).history = .allocate handle tool) :
    let state := run input C .uncapped accounting rule sample clock
    run input C .uncapped accounting rule sample (clock + 1) =
      record accounting state (.allocate handle tool) [.committed handle tool]
        (allocateLedger state handle tool) state.cursor false := by
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  obtain ⟨next, hstep⟩ := hlegal sample.1 _ _ clock _ hp hactive
  have hr := run_succ_of_step input C .uncapped accounting rule sample clock next hactive hstep
  rw [haction] at hstep
  cases hstep
  exact hr

theorem menu_run_execute (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (sample : Seed × input.World)
    (clock : ℕ) (handle : MismatchHandle I) (tool : I.Tool)
    (hactive : (run input C .uncapped accounting rule sample clock).halted = false)
    (haction : rule sample.1 (run input C .uncapped accounting rule sample clock).history = .execute handle tool) :
    let state := run input C .uncapped accounting rule sample clock
    run input C .uncapped accounting rule sample (clock + 1) =
      record accounting state (.execute handle tool) [.executed handle tool]
        (executeLedger state handle tool) state.cursor false := by
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  obtain ⟨next, hstep⟩ := hlegal sample.1 _ _ clock _ hp hactive
  have hr := run_succ_of_step input C .uncapped accounting rule sample clock next hactive hstep
  rw [haction] at hstep
  cases hstep
  exact hr

theorem menu_run_advance (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (sample : Seed × input.World)
    (clock : ℕ) (stage : I.Stage)
    (hactive : (run input C .uncapped accounting rule sample clock).halted = false)
    (haction : rule sample.1 (run input C .uncapped accounting rule sample clock).history = .advance stage) :
    let state := run input C .uncapped accounting rule sample clock
    run input C .uncapped accounting rule sample (clock + 1) =
      record accounting state (.advance stage) [.advanced stage]
        (advanceLedger state stage) (state.cursor + 1) false := by
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  obtain ⟨next, hstep⟩ := hlegal sample.1 _ _ clock _ hp hactive
  have hr := run_succ_of_step input C .uncapped accounting rule sample clock next hactive hstep
  rw [haction] at hstep
  cases hstep
  exact hr

theorem menu_run_stop (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (sample : Seed × input.World)
    (clock : ℕ) (hactive : (run input C .uncapped accounting rule sample clock).halted = false)
    (haction : rule sample.1 (run input C .uncapped accounting rule sample clock).history = .stop) :
    run input C .uncapped accounting rule sample (clock + 1) =
      stopState (run input C .uncapped accounting rule sample clock) false := by
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  obtain ⟨next, hstep⟩ := hlegal sample.1 _ _ clock _ hp hactive
  have hr := run_succ_of_step input C .uncapped accounting rule sample clock next hactive hstep
  rw [haction] at hstep
  cases hstep
  exact hr

theorem menu_run_abandon (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (sample : Seed × input.World)
    (clock : ℕ) (hactive : (run input C .uncapped accounting rule sample clock).halted = false)
    (haction : rule sample.1 (run input C .uncapped accounting rule sample clock).history = .abandon) :
    run input C .uncapped accounting rule sample (clock + 1) =
      stopState (run input C .uncapped accounting rule sample clock) true := by
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  obtain ⟨next, hstep⟩ := hlegal sample.1 _ _ clock _ hp hactive
  have hr := run_succ_of_step input C .uncapped accounting rule sample clock next hactive hstep
  rw [haction] at hstep
  cases hstep
  exact hr

end PDMenu
