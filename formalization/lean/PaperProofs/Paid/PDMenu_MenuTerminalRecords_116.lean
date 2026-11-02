module

public import PaperProofs.Paid.PDMenu_MenuEntryRecordTarget_115
public import PaperProofs.Paid.PDMenu_MenuNativeActionRun_103

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem menuEntryRunRecords_zero (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (cursor clock : ℕ) (hfit : cursor + 0 = N)
    (hentry : FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) cursor clock sample) :
    MenuEntryRunRecords P N K table fee hfee C accounting sample cursor 0 clock hfit := by
  let input := P.freshInput N K fee hfee
  let rule := P.compiledMenuRule N K table
  have hlegal := P.compiledMenuRule_uncapped_legal N K table fee hfee C hearly accounting
  have hactive := (firstEntryAt_unborn input C .uncapped accounting rule hlegal sample cursor clock hentry).1
  have hc : (run input C .uncapped accounting rule sample clock).cursor = N := by
    have hcursor : (run input C .uncapped accounting rule sample clock).cursor = cursor := hentry.1
    exact hcursor.trans (by simpa only [Nat.add_zero] using hfit)
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  have haction : rule sample.1 (run input C .uncapped accounting rule sample clock).history = .stop :=
    compiledMenuRule_terminal_stop P N K table fee hfee C hearly accounting rule sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hp sample.1 hactive hc
  have hstop := menu_run_stop input C accounting rule hlegal sample clock hactive haction
  have hhalt : (run input C .uncapped accounting rule sample (clock + 1)).halted = true := by rw [hstop]; rfl
  obtain ⟨m, _, hpEnd⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample (clock + 1)
  have hcEnd : (run input C .uncapped accounting rule sample (clock + 1)).cursor = N := by rw [hstop]; exact hc
  have haEnd : (run input C .uncapped accounting rule sample (clock + 1)).ledger.abandoned = false := by rw [hstop]; rfl
  have hsuccess : runSuccess input C .uncapped accounting rule sample :=
    ⟨clock + 1, hhalt, menuPrefix_terminal_success P N K table fee hfee C hearly accounting sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hpEnd hcEnd hhalt haEnd⟩
  simp only [MenuEntryRunRecords, menuPathSummary_zero, menuPathFinish]
  refine ⟨clock + 1, Nat.le_succ clock, hhalt, ?_, ?_, ?_⟩
  · rw [hstop]
    exact (add_zero _).symm
  · rw [hstop]
    exact (Nat.add_zero _).symm
  · constructor
    · intro _
      trivial
    · intro _
      exact hsuccess

end PDMenu
