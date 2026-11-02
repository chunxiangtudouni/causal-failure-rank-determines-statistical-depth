module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_009
public import PaperProofs.Paid.PDROC_CalibratedRuntime_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu
open scoped ENNReal

namespace PDROC.CalibratedRuntime

theorem entryRecords_abandon (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedMenuSeed × (P.input fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = P.certificate.stages)
    (stage : P.sharedInstance.Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.input fee hfee) C .uncapped accounting (menuRule P table) cursor clock sample)
    (ha : (menuEntryAt table (n + 1) (P.tools -
      (run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.executions.length)).action = .abandon ∨
      (menuEntryAt table (n + 1) (P.tools -
      (run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.executions.length)).action = .finish) :
    EntryRecords P table fee hfee C accounting sample cursor (n + 1) clock hfit := by
  let input := P.input fee hfee
  let rule := menuRule P table
  let start := run input C .uncapped accounting rule sample clock
  have hlegal := menuRule_legal P table fee hfee C hearly accounting
  obtain ⟨hactive, hfresh⟩ := firstEntryAt_unborn input C .uncapped accounting rule hlegal sample cursor clock hentry
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  have hcursor : start.cursor = stage.val := hentry.1.trans hstage.symm
  have hport : start.ledger.written stage = none := (hfresh stage (by omega)).1
  have hk := menuPrefix_entryTools_eq_physical_sub P table fee hfee C accounting sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) hp stage hcursor hport
  have hrow : P.certificate.stages - stage.val = n + 1 := by omega
  obtain ⟨hh, hc, hw, _⟩ := menuFirstEntry_visible_fresh input C .uncapped accounting rule hlegal sample stage clock
    (hstage.symm ▸ hentry)
  have haction : rule sample.1 start.history = .abandon := by
    let choose : MenuAction → Action P.sharedInstance := fun action => match action with
      | .finish | .abandon => .abandon
      | .test level _ => P.calibratedTestingAction level sample.1 start.history stage
    have hf : rule sample.1 start.history = choose ((menuEntryAt table (P.certificate.stages - stage.val)
        (P.menuEntryTools P.certificate.stages P.tools start.history stage)).action) :=
      menuRule_unwrittenFrame P table sample.1 start.history stage hh hc hw
    have he := congrArg₂ (fun remaining tools => (menuEntryAt table remaining tools).action) hrow hk
    rcases ha with ha | ha
    · exact hf.trans (congrArg choose (he.trans ha))
    · exact hf.trans (congrArg choose (he.trans ha))
  apply entryRecords_of_immediate_abandon P table fee hfee C hearly accounting sample cursor (n + 1) clock hfit hentry haction
  exact pathSummary_abandon P (calibratedFamily P) table n _ _ _ ha

theorem entryRecords_invalid_level (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedMenuSeed × (P.input fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = P.certificate.stages)
    (stage : P.sharedInstance.Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.input fee hfee) C .uncapped accounting (menuRule P table) cursor clock sample)
    (level : ℕ) (bad : MenuBadAction) (invalid : ¬level ≤ P.certificate.M)
    (ha : (menuEntryAt table (n + 1) (P.tools -
      (run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.executions.length)).action = .test level bad) :
    EntryRecords P table fee hfee C accounting sample cursor (n + 1) clock hfit := by
  let input := P.input fee hfee
  let rule := menuRule P table
  let start := run input C .uncapped accounting rule sample clock
  have hlegal := menuRule_legal P table fee hfee C hearly accounting
  obtain ⟨hactive, hfresh⟩ := firstEntryAt_unborn input C .uncapped accounting rule hlegal sample cursor clock hentry
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  have hcursor : start.cursor = stage.val := hentry.1.trans hstage.symm
  have hport : start.ledger.written stage = none := (hfresh stage (by omega)).1
  have hk := menuPrefix_entryTools_eq_physical_sub P table fee hfee C accounting sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) hp stage hcursor hport
  have hrow : P.certificate.stages - stage.val = n + 1 := by omega
  obtain ⟨hh, hc, hw, _⟩ := menuFirstEntry_visible_fresh input C .uncapped accounting rule hlegal sample stage clock
    (hstage.symm ▸ hentry)
  have haction : rule sample.1 start.history = .abandon := by
    let choose : MenuAction → Action P.sharedInstance := fun action => match action with
      | .finish | .abandon => .abandon
      | .test level _ => P.calibratedTestingAction level sample.1 start.history stage
    have hf : rule sample.1 start.history = choose ((menuEntryAt table (P.certificate.stages - stage.val)
        (P.menuEntryTools P.certificate.stages P.tools start.history stage)).action) :=
      menuRule_unwrittenFrame P table sample.1 start.history stage hh hc hw
    have he := (congrArg₂ (fun remaining tools => (menuEntryAt table remaining tools).action) hrow hk).trans ha
    have hchosen : choose (.test level bad) = .abandon := by
      change P.calibratedTestingAction level sample.1 start.history stage = .abandon
      have hz : level ≠ 0 := by omega
      simp only [calibratedTestingAction, hz, ite_false, dite_eq_right invalid]
    exact hf.trans ((congrArg choose he).trans hchosen)
  apply entryRecords_of_immediate_abandon P table fee hfee C hearly accounting sample cursor (n + 1) clock hfit hentry haction
  exact pathSummary_invalid P (calibratedFamily P) table n _ level bad _ _ ha
    (calibratedFamily_none P level invalid)

theorem entryRecords_test_abort (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedMenuSeed × (P.input fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = P.certificate.stages)
    (stage : P.sharedInstance.Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.input fee hfee) C .uncapped accounting (menuRule P table) cursor clock sample)
    (level reviews : ℕ) (bad : MenuBadAction) (valid : level ≤ P.certificate.M)
    (ha : (menuEntryAt table (n + 1) (P.tools -
      (run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.executions.length)).action = .test level bad)
    (hstop : (calibratedStageTest P level).rule.stop (sample.1.1 stage, sample.1.2 stage)
      (worldTapes (P.input fee hfee) sample.2 stage) = reviews)
    (hwrong : (calibratedStageTest P level).rule.decision (sample.1.1 stage, sample.1.2 stage)
      (worldTapes (P.input fee hfee) sample.2 stage) ≠ (P.input fee hfee).truthAt sample.2 stage)
    (habort : bad = .abandon ∨ P.tools -
      (run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.executions.length = 0) :
    EntryRecords P table fee hfee C accounting sample cursor (n + 1) clock hfit := by
  let input := P.input fee hfee
  let rule := menuRule P table
  let start := run input C .uncapped accounting rule sample clock
  let writeclock := clock + reviews + 1
  let written := run input C .uncapped accounting rule sample writeclock
  let ended := writeclock + 1
  let bit := (calibratedStageTest P level).rule.decision (sample.1.1 stage, sample.1.2 stage)
    (worldTapes input sample.2 stage)
  let k := P.tools - start.ledger.executions.length
  have hlegal := menuRule_legal P table fee hfee C hC.1.1 accounting
  obtain ⟨hactive, hcursor, hwritten, htruth, hobs, hexecutions, hsnapshot, havailable, hnoCurrent⟩ :=
    menuEntry_written_records P table fee hfee C hC accounting sample cursor n clock hfit stage hstage
      hentry level reviews bad valid ha hstop
  replace hexecutions : written.ledger.executions = start.ledger.executions := hexecutions
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample writeclock hactive
  have hcStage : written.cursor = stage.val := hcursor.trans hstage.symm
  have hbad : bit ≠ written.ledger.truth stage := fun he => hwrong (he.trans (congrFun htruth stage))
  have hrow : P.certificate.stages - stage.val = n + 1 := by omega
  have hcell : (menuEntryAt table (P.certificate.stages - stage.val)
      (P.menuEntryTools P.certificate.stages P.tools written.history stage)).action = .test level bad := by
    exact (congrArg₂ (fun remaining tools => (menuEntryAt table remaining tools).action) hrow hsnapshot).trans ha
  have haction : rule sample.1 written.history = .abandon := by
    cases bad with
    | abandon =>
      have hf := menuRule_written_wrong P table fee hfee C hC.1.1 accounting rule sample.1
        (input.truthAt sample.2) (worldTapes input sample.2) hp sample.1 stage bit hactive hcStage hwritten hbad
      exact hf.trans (congrArg (fun action : MenuAction => match action with
        | .test _ .repair => P.menuRepairAction P.certificate.stages P.tools written.history stage
        | _ => .abandon) hcell)
    | repair =>
      have hz : k = 0 := habort.resolve_left (by intro h; cases h)
      apply menuRule_fresh_repair_no_tool P table fee hfee C hC.1.1 accounting rule sample.1
        (input.truthAt sample.2) (worldTapes input sample.2) hp sample.1 stage bit level
        hactive hcStage hwritten hbad hcell hnoCurrent
      exact havailable.trans hz
  have hr := menu_run_abandon input C accounting rule hlegal sample writeclock hactive haction
  have hhalt : (run input C .uncapped accounting rule sample ended).halted = true := by rw [hr]; rfl
  have hfailure : ¬runSuccess input C .uncapped accounting rule sample := by
    intro hs
    have hbad := ((menu_runSuccess_iff_of_halted input C .uncapped accounting rule sample ended hhalt).mp hs).2.1
    rw [hr] at hbad
    change true = false at hbad
    cases hbad
  obtain ⟨m, _, hpEnd⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample ended
  have hcausal := prefix_cursorInvariant input C .uncapped accounting rule sample.1 _ _ hpEnd
  have hchild : TraceLedgerMatch P (cursor + 1) (historyUsed start.history) [] written
      (run input C .uncapped accounting rule sample ended) := by
    apply traceLedgerMatch_nil
    · intro other hs
      apply hcausal.future_written
      have hc : (run input C .uncapped accounting rule sample ended).cursor = cursor := by rw [hr]; exact hcursor
      rw [hc]
      omega
    · rw [hr]
      rfl
  have hhead : ∀ other : P.sharedInstance.Stage, other.val = cursor →
      (run input C .uncapped accounting rule sample ended).ledger.written other =
        some (!(run input C .uncapped accounting rule sample ended).ledger.truth other) := by
    intro other ho
    have heq : other = stage := Fin.ext (ho.trans hstage.symm)
    subst other
    rw [hr]
    exact hwritten.trans (congrArg some (Bool.eq_not_iff.mpr hbad))
  have hpairs : executionPairs P written.ledger = executionPairs P start.ledger := by
    exact congrArg (fun executions : List (Execution P.sharedInstance) =>
      executions.map fun execution => (execution.handle.stage.val, (show Fin P.tools from execution.tool))) hexecutions
  have htrace : TraceLedgerMatch P cursor (historyUsed start.history) [(true, false)] start
      (run input C .uncapped accounting rule sample ended) :=
    traceLedgerMatch_cons_noRepair P cursor (historyUsed start.history) true [] start written _ hhead hpairs hchild
  have hseed := calibratedSuffixSeed_head P cursor n hfit sample.1 stage hstage
  have hworld := menuSuffixWorld_head P P.certificate.stages P.tools cursor n hfit fee hfee sample.2 stage hstage
  have hstopCrop : (calibratedStageTest P level).rule.stop
      (calibratedSuffixSeed P cursor (n + 1) hfit sample.1 0)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2 0).2 = reviews := by
    rw [hseed, hworld]
    exact hstop
  have hwrongCrop : (calibratedStageTest P level).rule.decision
      (calibratedSuffixSeed P cursor (n + 1) hfit sample.1 0)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2 0).2 ≠
        (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2 0).1 := by
    rw [hseed, hworld]
    exact hwrong
  have hsummary : pathSummary P (calibratedFamily P) table (n + 1) k
      (calibratedSuffixSeed P cursor (n + 1) hfit sample.1)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2) =
        { observation := P.experiment.observationCharge reviews, trace := [(true, false)], failure := true } := by
    cases bad with
    | abandon =>
      exact pathSummary_test_abandon P (calibratedFamily P) table n k level reviews
        (calibratedStageTest P level) _ _ ha (calibratedFamily_some P level valid) hstopCrop hwrongCrop
    | repair =>
      have hz : k = 0 := habort.resolve_left (by intro h; cases h)
      have ha0 : (menuEntryAt table (n + 1) 0).action = .test level .repair :=
        (congrArg (fun tools => (menuEntryAt table (n + 1) tools).action) hz.symm).trans ha
      have hs0 := pathSummary_test_no_tool P (calibratedFamily P) table n level reviews
        (calibratedStageTest P level)
        (calibratedSuffixSeed P cursor (n + 1) hfit sample.1)
        (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2)
        ha0 (calibratedFamily_some P level valid) hstopCrop hwrongCrop
      exact (congrArg (fun tools => pathSummary P (calibratedFamily P) table (n + 1) tools
        (calibratedSuffixSeed P cursor (n + 1) hfit sample.1)
        (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2)) hz).trans hs0
  unfold EntryRecords
  dsimp only
  rw [hsummary]
  refine ⟨ended, (by dsimp only [ended, writeclock]; omega), hhalt, ?_, htrace, ?_⟩
  · rw [hr]
    exact hobs
  · exact ⟨fun hs => (hfailure hs).elim, fun hfalse => Bool.noConfusion hfalse⟩

end PDROC.CalibratedRuntime
