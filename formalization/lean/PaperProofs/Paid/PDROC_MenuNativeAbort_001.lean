module

public import PaperProofs.Paid.PDMenu_MenuWrittenEntryRecords_119
public import PaperProofs.Paid.PDMenu_MenuEntryRecordTarget_115
public import PaperProofs.Paid.PDMenu_MenuEmptyRepair_111
public import PaperProofs.Paid.PDMenu_MenuNativeActionRun_103

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

/-- A genuinely reached wrong write either explicitly abandons or has no
remaining physical tool. The next actual step is exactly the original abort. -/
theorem menuEntry_test_abort_run (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = N)
    (stage : (freshInstance N K).Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) cursor clock sample)
    (level reviews : ℕ) (bad : MenuBadAction)
    (ha : (Parameters.menuEntryAt table (n + 1)
      (K - (run (P.freshInput N K fee hfee) C .uncapped accounting
        (P.compiledMenuRule N K table) sample clock).ledger.executions.length)).action = .test level bad)
    (hstop : (PDMenu.menuAnalysisTest P level).rule.stop (sample.1 stage)
      (PDMenu.menuOriginalTape P N K fee hfee stage
        (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) = reviews)
    (hwrong : (PDMenu.menuAnalysisTest P level).rule.decision (sample.1 stage)
      (PDMenu.menuOriginalTape P N K fee hfee stage
        (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) ≠
      (P.freshInput N K fee hfee).truthAt sample.2 stage)
    (habort : bad = .abandon ∨ K - (run (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) sample clock).ledger.executions.length = 0) :
    run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table)
        sample (clock + reviews + 2) =
      stopState (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table)
        sample (clock + reviews + 1)) true := by
  let input := P.freshInput N K fee hfee
  let rule := P.compiledMenuRule N K table
  let writeclock := clock + reviews + 1
  let written := run input C .uncapped accounting rule sample writeclock
  have hearly : C.reporting = .early := hC.1.1
  have hlegal := P.compiledMenuRule_uncapped_legal N K table fee hfee C hearly accounting
  obtain ⟨hactive, hcursor, hwritten, htruth, _, _, htools, havailable, hnoCurrent⟩ :=
    PDMenu.menuEntry_written_records P N K table fee hfee C hC accounting sample cursor n clock hfit
      stage hstage hentry level reviews bad ha hstop
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample writeclock hactive
  have hcStage : written.cursor = stage.val := hcursor.trans hstage.symm
  have hwrongWritten : (PDMenu.menuAnalysisTest P level).rule.decision (sample.1 stage)
      (PDMenu.menuOriginalTape P N K fee hfee stage (worldTapes input sample.2 stage)) ≠
      written.ledger.truth stage := by
    rw [htruth]
    exact hwrong
  have hrow : N - stage.val = n + 1 := by omega
  have hcell : (Parameters.menuEntryAt table (N - stage.val)
      (P.menuEntryTools N K written.history stage)).action = .test level bad := by
    rw [hrow, htools]
    exact ha
  have haction : rule sample.1 written.history = .abandon := by
    cases bad with
    | abandon =>
      exact PDMenu.compiledMenuRule_written_abandon P N K table fee hfee C hearly accounting
        rule sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp sample.1 stage _ level
        hactive hcStage hwritten hwrongWritten hcell
    | repair =>
      have hzero := habort.resolve_left (by decide)
      have havailableZero : (Finset.univ \ historyUsed written.history).card = 0 :=
        havailable.trans hzero
      exact PDMenu.compiledMenuRule_fresh_repair_no_tool P N K table fee hfee C hearly accounting
        rule sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp sample.1 stage _ level
        hactive hcStage hwritten hwrongWritten hcell hnoCurrent havailableZero
  have hrun := PDMenu.menu_run_abandon input C accounting rule hlegal sample writeclock hactive haction
  have ht : writeclock + 1 = clock + reviews + 2 := by omega
  rw [ht] at hrun
  exact hrun

/-- Exact entry records for both wrong terminal branches, without any
continuation/IH, expected-value or future-policy premise. -/
theorem menuEntryRunRecords_test_abort (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = N)
    (stage : (freshInstance N K).Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) cursor clock sample)
    (level reviews : ℕ) (bad : MenuBadAction)
    (ha : (Parameters.menuEntryAt table (n + 1)
      (K - (run (P.freshInput N K fee hfee) C .uncapped accounting
        (P.compiledMenuRule N K table) sample clock).ledger.executions.length)).action = .test level bad)
    (hstop : (PDMenu.menuAnalysisTest P level).rule.stop (sample.1 stage)
      (PDMenu.menuOriginalTape P N K fee hfee stage
        (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) = reviews)
    (hwrong : (PDMenu.menuAnalysisTest P level).rule.decision (sample.1 stage)
      (PDMenu.menuOriginalTape P N K fee hfee stage
        (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) ≠
      (P.freshInput N K fee hfee).truthAt sample.2 stage)
    (habort : bad = .abandon ∨ K - (run (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) sample clock).ledger.executions.length = 0) :
    PDMenu.MenuEntryRunRecords P N K table fee hfee C accounting sample cursor (n + 1) clock hfit := by
  let input := P.freshInput N K fee hfee
  let rule := P.compiledMenuRule N K table
  let start := run input C .uncapped accounting rule sample clock
  let k := K - start.ledger.executions.length
  have habandon := menuEntry_test_abort_run P N K table fee hfee C hC accounting sample cursor n clock hfit
    stage hstage hentry level reviews bad ha hstop hwrong habort
  obtain ⟨_, _, _, _, hobs, hexecutions, _, _, _⟩ :=
    PDMenu.menuEntry_written_records P N K table fee hfee C hC accounting sample cursor n clock hfit
      stage hstage hentry level reviews bad ha hstop
  have hhalt : (run input C .uncapped accounting rule sample (clock + reviews + 2)).halted = true := by
    rw [habandon]
    rfl
  have hfailure : ¬runSuccess input C .uncapped accounting rule sample := by
    intro hs
    have hsuccess := (PDMenu.menu_runSuccess_iff_of_halted input C .uncapped accounting rule sample
      (clock + reviews + 2) hhalt).mp hs
    have hbad := hsuccess.2.1
    rw [habandon] at hbad
    change true = false at hbad
    cases hbad
  have hseed := PDMenu.menuSuffixSeed_head N K cursor n hfit sample.1 stage hstage
  have hworld := PDMenu.menuSuffixWorld_head P N K cursor n hfit fee hfee sample.2 stage hstage
  have hstopCrop : (PDMenu.menuAnalysisTest P level).rule.stop
      (PDMenu.menuSuffixSeed N K cursor (n + 1) hfit sample.1 0)
      (PDMenu.menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2 0).2 = reviews := by
    rw [hseed, hworld]
    exact hstop
  have hwrongCrop : (PDMenu.menuAnalysisTest P level).rule.decision
      (PDMenu.menuSuffixSeed N K cursor (n + 1) hfit sample.1 0)
      (PDMenu.menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2 0).2 ≠
        (PDMenu.menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2 0).1 := by
    rw [hseed, hworld]
    exact hwrong
  have hsummary : PDMenu.menuPathSummary P table (n + 1) k
      (PDMenu.menuSuffixSeed N K cursor (n + 1) hfit sample.1)
      (PDMenu.menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2) =
        (⟨P.experiment.observationCharge reviews, 0, true⟩ : PDMenu.MenuPathRecord) := by
    cases bad with
    | abandon =>
      simpa only [PDMenu.menuPathAbandon, add_zero] using PDMenu.menuPathSummary_test_abandon P table n k level reviews
        (PDMenu.menuSuffixSeed N K cursor (n + 1) hfit sample.1)
        (PDMenu.menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2) ha hstopCrop hwrongCrop
    | repair =>
      have hzero : k = 0 := habort.resolve_left (by decide)
      rw [hzero]
      have haZero : (Parameters.menuEntryAt table (n + 1) 0).action = .test level .repair := by
        rw [← hzero]
        exact ha
      simpa only [PDMenu.menuPathAbandon, add_zero] using PDMenu.menuPathSummary_test_no_tool P table n level reviews
        (PDMenu.menuSuffixSeed N K cursor (n + 1) hfit sample.1)
        (PDMenu.menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2) haZero hstopCrop hwrongCrop
  unfold PDMenu.MenuEntryRunRecords
  dsimp only
  rw [hsummary]
  refine ⟨clock + reviews + 2, (by omega), hhalt, ?_, ?_, ?_⟩
  · rw [habandon]
    exact hobs
  · rw [habandon]
    exact (congrArg List.length hexecutions).trans (Nat.add_zero _).symm
  · constructor
    · intro hs
      exact (hfailure hs).elim
    · intro hfalse
      cases hfalse

end PDROC
