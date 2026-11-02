module

public import PaperProofs.Paid.PDMenu_MenuWrittenFrame_097

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem compiledMenu_run_correct_advance (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (stage : (freshInstance N K).Stage) (clock : ℕ)
    (hactive : (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).halted = false)
    (hcursor : (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).cursor = stage.val)
    (hbit : (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).ledger.written stage =
      some ((run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).ledger.truth stage)) :
    let state := run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock
    run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample (clock + 1) =
      record accounting state (.advance stage) [.advanced stage] (advanceLedger state stage) (state.cursor + 1) false := by
  let input := P.freshInput N K fee hfee
  let rule := P.compiledMenuRule N K table
  have hp := run_prefix_of_active input C .uncapped accounting rule
    (P.compiledMenuRule_uncapped_legal N K table fee hfee C hearly accounting) sample clock hactive
  have haction := compiledMenuRule_written_correct P N K table fee hfee C hearly accounting rule sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) hp sample.1 stage hactive hcursor hbit
  have haction' : rule sample.1 (run input C .uncapped accounting rule sample clock).history = .advance stage := haction
  apply run_succ_of_step input C .uncapped accounting rule sample clock _ hactive
  rw [haction']
  exact Step.advance _ stage ⟨hactive, hcursor⟩ (by rw [hbit]; exact Option.some_ne_none _) (.inl rfl)

/-- Monotonicity turns an actual cursor increment into genuine first entry,
without a separate external entry-clock correspondence premise. -/
theorem menuFirstEntryAfterAdvance {I : Instance} {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (clock cursor : ℕ) (hcursor : (run input C mode accounting rule sample clock).cursor = cursor)
    (hnext : (run input C mode accounting rule sample (clock + 1)).cursor = cursor + 1) :
    FirstEntryAt input C mode accounting rule (cursor + 1) (clock + 1) sample := by
  refine ⟨hnext, ?_⟩
  intro j hj hsame
  have hle := run_cursor_monotone input C mode accounting rule hlegal sample (Nat.le_of_lt_succ hj)
  change (run input C mode accounting rule sample j).cursor ≤ (run input C mode accounting rule sample clock).cursor at hle
  rw [hsame, hcursor] at hle
  exact Nat.not_succ_le_self cursor hle

end PDMenu
