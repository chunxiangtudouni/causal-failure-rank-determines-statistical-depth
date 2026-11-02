module

public import PaperProofs.Paid.PDMenu_MenuEntryRun_096
public import PaperProofs.Paid.PDMenu_MenuSuffixSample_110
public import PaperProofs.Paid.PDMenu_MenuPhysicalSnapshot_084

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem menuSuffixSeed_head (N K cursor n : ℕ) (hfit : cursor + (n + 1) = N)
    (seed : MenuSeed N K) (stage : (freshInstance N K).Stage) (hstage : stage.val = cursor) :
    menuSuffixSeed N K cursor (n + 1) hfit seed 0 = seed stage :=
  congrArg seed (menuSuffixStage_zero N K cursor n hfit stage hstage)

theorem menuSuffixWorld_head (P : Parameters) (N K cursor n : ℕ) (hfit : cursor + (n + 1) = N)
    (fee : ℚ) (hfee : 0 ≤ fee) (world : (P.freshInput N K fee hfee).World)
    (stage : (freshInstance N K).Stage) (hstage : stage.val = cursor) :
    menuSuffixWorld P N K cursor (n + 1) hfit fee hfee world 0 = world stage :=
  congrArg (α := (freshInstance N K).Stage) (β := Bool × P.experiment.Tape) (fun stage => world stage)
    (menuSuffixStage_zero N K cursor n hfit stage hstage)

theorem menuEntry_run_written (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = N)
    (stage : (freshInstance N K).Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) cursor clock sample)
    (level reviews : ℕ) (bad : MenuBadAction)
    (ha : (Parameters.menuEntryAt table (n + 1)
      (K - (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).ledger.executions.length)).action = .test level bad)
    (hstop : (menuAnalysisTest P level).rule.stop (sample.1 stage)
      (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) = reviews) :
    run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample (clock + reviews + 1) =
      menuWrittenFrom (P.freshInput N K fee hfee) C accounting stage
        (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock)
        (worldTapes (P.freshInput N K fee hfee) sample.2 stage) reviews
        ((menuAnalysisTest P level).rule.decision (sample.1 stage)
          (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage))) := by
  let input := P.freshInput N K fee hfee
  let rule := P.compiledMenuRule N K table
  have hlegal := P.compiledMenuRule_uncapped_legal N K table fee hfee C hearly accounting
  have hentry' : FirstEntryAt input C .uncapped accounting rule stage.val clock sample := hstage.symm ▸ hentry
  have hactive := (firstEntryAt_unborn input C .uncapped accounting rule hlegal sample cursor clock hentry).1
  have hport := ((firstEntryAt_unborn input C .uncapped accounting rule hlegal sample cursor clock hentry).2 stage (by omega)).1
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  have hc : (run input C .uncapped accounting rule sample clock).cursor = stage.val := hentry.1.trans hstage.symm
  have hk := menuPrefix_entryTools_eq_physical_sub P N K table fee hfee C accounting sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) hp stage hc hport
  have hrow : N - stage.val = n + 1 := by omega
  apply compiledMenu_run_writtenFrom_firstEntry P N K table fee hfee C hearly accounting sample stage clock level reviews bad hentry'
  · rw [hrow, hk]
    exact ha
  · exact hstop

end PDMenu
