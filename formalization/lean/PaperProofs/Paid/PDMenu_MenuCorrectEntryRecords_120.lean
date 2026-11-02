module

public import PaperProofs.Paid.PDMenu_MenuWrittenEntryRecords_119
public import PaperProofs.Paid.PDMenu_MenuEntryRecordTarget_115
public import PaperProofs.Paid.PDMenu_MenuSummaryBranches_113

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Correct local branch of the strict remaining-stage induction. The IH
is only used at the genuinely reached shorter entry in this same physical
run; the final induction will discharge it rather than expose it as a
Policy-performance premise. -/
theorem menuEntryRunRecords_test_correct (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = N) (hnextfit : cursor + 1 + n = N)
    (stage : (freshInstance N K).Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) cursor clock sample)
    (level reviews : ℕ) (bad : MenuBadAction)
    (ha : (Parameters.menuEntryAt table (n + 1)
      (K - (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).ledger.executions.length)).action = .test level bad)
    (hstop : (menuAnalysisTest P level).rule.stop (sample.1 stage)
      (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) = reviews)
    (hcorrect : (menuAnalysisTest P level).rule.decision (sample.1 stage)
      (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) =
        (P.freshInput N K fee hfee).truthAt sample.2 stage)
    (ih : ∀ nextclock, FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) (cursor + 1) nextclock sample →
        MenuEntryRunRecords P N K table fee hfee C accounting sample (cursor + 1) n nextclock hnextfit) :
    MenuEntryRunRecords P N K table fee hfee C accounting sample cursor (n + 1) clock hfit := by
  let input := P.freshInput N K fee hfee
  let rule := P.compiledMenuRule N K table
  let start := run input C .uncapped accounting rule sample clock
  let writeclock := clock + reviews + 1
  let written := run input C .uncapped accounting rule sample writeclock
  let nextclock := writeclock + 1
  let k := K - start.ledger.executions.length
  let child := menuPathSummary P table n k
    (menuSuffixSeed N K (cursor + 1) n hnextfit sample.1)
    (menuSuffixWorld P N K (cursor + 1) n hnextfit fee hfee sample.2)
  have hlegal := P.compiledMenuRule_uncapped_legal N K table fee hfee C hC.1.1 accounting
  obtain ⟨hactive, hcursor, hwritten, htruth, hobs, hexecutions, _, _, _⟩ :=
    menuEntry_written_records P N K table fee hfee C hC accounting sample cursor n clock hfit stage hstage
      hentry level reviews bad ha hstop
  have hcStage : written.cursor = stage.val := hcursor.trans hstage.symm
  have hgood : written.ledger.written stage = some (written.ledger.truth stage) :=
    hwritten.trans (congrArg some (hcorrect.trans (congrFun htruth stage).symm))
  have hadv := compiledMenu_run_correct_advance P N K table fee hfee C hC.1.1 accounting
    sample stage writeclock hactive hcStage hgood
  have hcNext : (run input C .uncapped accounting rule sample nextclock).cursor = cursor + 1 := by
    rw [hadv]
    exact congrArg (fun value : ℕ => value + 1) hcursor
  have hentryNext := menuFirstEntryAfterAdvance input C .uncapped accounting rule hlegal sample writeclock cursor hcursor hcNext
  have heNext : (run input C .uncapped accounting rule sample nextclock).ledger.executions.length = start.ledger.executions.length := by
    rw [hadv]
    exact congrArg List.length hexecutions
  have hoNext : (run input C .uncapped accounting rule sample nextclock).ledger.observationBill input.fees =
      start.ledger.observationBill input.fees + P.experiment.observationCharge reviews := by
    rw [hadv]
    exact hobs
  obtain ⟨ended, hended, hhalt, hoChild, heChild, hsChild⟩ := ih nextclock hentryNext
  rw [heNext] at hoChild heChild hsChild
  have hoChild' : (run input C .uncapped accounting rule sample ended).ledger.observationBill input.fees =
      (run input C .uncapped accounting rule sample nextclock).ledger.observationBill input.fees + child.observation := hoChild
  have heChild' : (run input C .uncapped accounting rule sample ended).ledger.executions.length =
      start.ledger.executions.length + child.physicalRepairs := heChild
  have hsChild' : runSuccess input C .uncapped accounting rule sample ↔ child.failure = false := hsChild
  have hseed := menuSuffixSeed_head N K cursor n hfit sample.1 stage hstage
  have hworld := menuSuffixWorld_head P N K cursor n hfit fee hfee sample.2 stage hstage
  have hstopCrop : (menuAnalysisTest P level).rule.stop
      (menuSuffixSeed N K cursor (n + 1) hfit sample.1 0)
      (menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2 0).2 = reviews := by
    rw [hseed, hworld]
    exact hstop
  have hcorrectCrop : (menuAnalysisTest P level).rule.decision
      (menuSuffixSeed N K cursor (n + 1) hfit sample.1 0)
      (menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2 0).2 =
        (menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2 0).1 := by
    rw [hseed, hworld]
    exact hcorrect
  have hsummary : menuPathSummary P table (n + 1) k
      (menuSuffixSeed N K cursor (n + 1) hfit sample.1)
      (menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2) =
        { child with observation := P.experiment.observationCharge reviews + child.observation } := by
    have hs := menuPathSummary_test_correct P table n k level reviews bad
      (menuSuffixSeed N K cursor (n + 1) hfit sample.1)
      (menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2) ha hstopCrop hcorrectCrop
    rw [menuSuffixSeed_tail N K cursor n hfit hnextfit, menuSuffixWorld_tail P N K cursor n hfit hnextfit fee hfee] at hs
    exact hs
  unfold MenuEntryRunRecords
  dsimp only
  rw [hsummary]
  refine ⟨ended, (by dsimp only [nextclock, writeclock] at hended; omega), hhalt, ?_, heChild', hsChild'⟩
  calc
    _ = (run input C .uncapped accounting rule sample nextclock).ledger.observationBill input.fees + child.observation := hoChild'
    _ = (start.ledger.observationBill input.fees + P.experiment.observationCharge reviews) + child.observation :=
      congrArg (fun charge => charge + child.observation) hoNext
    _ = _ := add_assoc _ _ _

end PDMenu
