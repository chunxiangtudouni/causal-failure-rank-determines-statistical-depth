module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_009
public import PaperProofs.Paid.PDROC_CalibratedRuntime_010
public import PaperProofs.Paid.PDMenu_MenuRepairEntryRecords_122

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu

namespace PDROC.CalibratedRuntime

theorem entryRecords_test_repair (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedMenuSeed × (P.input fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = P.certificate.stages) (hnextfit : cursor + 1 + n = P.certificate.stages)
    (stage : P.sharedInstance.Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.input fee hfee) C .uncapped accounting
      (menuRule P table) cursor clock sample)
    (level reviews : ℕ) (valid : level ≤ P.certificate.M)
    (ha : (Parameters.menuEntryAt table (n + 1)
      (P.tools - (run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.executions.length)).action = .test level .repair)
    (hstop : (calibratedStageTest P level).rule.stop (sample.1.1 stage, sample.1.2 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes (P.input fee hfee) sample.2 stage)) = reviews)
    (hwrong : (calibratedStageTest P level).rule.decision (sample.1.1 stage, sample.1.2 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes (P.input fee hfee) sample.2 stage)) ≠
        (P.input fee hfee).truthAt sample.2 stage)
    (hpos : 0 < P.tools - (run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.executions.length)
    (ih : ∀ nextclock, FirstEntryAt (P.input fee hfee) C .uncapped accounting
      (menuRule P table) (cursor + 1) nextclock sample →
        EntryRecords P table fee hfee C accounting sample (cursor + 1) n nextclock hnextfit) :
    EntryRecords P table fee hfee C accounting sample cursor (n + 1) clock hfit := by
  let input := P.input fee hfee
  let rule := menuRule P table
  let start := run input C .uncapped accounting rule sample clock
  let writeclock := clock + reviews + 1
  let written := run input C .uncapped accounting rule sample writeclock
  let nextclock := writeclock + 3
  let k := P.tools - start.ledger.executions.length
  let bit := (calibratedStageTest P level).rule.decision (sample.1.1 stage, sample.1.2 stage)
    (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes input sample.2 stage))
  let child := pathSummary P (calibratedFamily P) table n (k - 1)
    (calibratedSuffixSeed P (cursor + 1) n hnextfit sample.1)
    (menuSuffixWorld P P.certificate.stages P.tools (cursor + 1) n hnextfit fee hfee sample.2)
  obtain ⟨hactive, hcursor, hwritten, htruth, hobs, hexecutions, hsnapshot, havailable, hnoCurrent⟩ :=
    menuEntry_written_records P table fee hfee C hC accounting sample cursor n clock hfit stage hstage
      hentry level reviews .repair valid ha hstop
  have hcStage : written.cursor = stage.val := hcursor.trans hstage.symm
  replace hexecutions : written.ledger.executions = start.ledger.executions := hexecutions
  have hbad : bit ≠ written.ledger.truth stage := fun he => hwrong (he.trans (congrFun htruth stage))
  have hrow : P.certificate.stages - stage.val = n + 1 := by omega
  have hcell : (Parameters.menuEntryAt table (P.certificate.stages - stage.val) (P.menuEntryTools P.certificate.stages P.tools written.history stage)).action = .test level .repair := by
    exact (congrArg₂ (fun remaining tools => (menuEntryAt table remaining tools).action) hrow hsnapshot).trans ha
  have htools : 0 < (Finset.univ \ historyUsed written.history).card := by
    exact lt_of_lt_of_eq hpos havailable.symm
  obtain ⟨selectedTool, hfind, _, _, hadv, hentryNext⟩ := menu_run_repair_threeSteps P table fee hfee C hC.1.1 accounting
    sample stage writeclock bit level hactive hcStage hwritten hbad hcell hnoCurrent htools
  let tool : Fin P.tools := selectedTool
  have hrNext : run input C .uncapped accounting rule sample nextclock = menuRepairedFrom accounting stage written tool := hadv
  have hentryNext' : FirstEntryAt input C .uncapped accounting rule (cursor + 1) nextclock sample := by
    have ht : FirstEntryAt input C .uncapped accounting rule (stage.val + 1) nextclock sample := hentryNext
    simpa only [hstage] using ht
  have heNext : (run input C .uncapped accounting rule sample nextclock).ledger.executions.length = start.ledger.executions.length + 1 := by
    exact (congrArg (fun state : State P.sharedInstance => state.ledger.executions.length) hrNext).trans
      ((menuRepairedFrom_executionCount accounting stage written tool).trans
        (congrArg (fun count : ℕ => count + 1) (congrArg List.length hexecutions)))
  have hkNext : P.tools - (run input C .uncapped accounting rule sample nextclock).ledger.executions.length = k - 1 := by
    rw [heNext, Nat.sub_add_eq]
  have hoNext : (run input C .uncapped accounting rule sample nextclock).ledger.observationBill input.fees =
      start.ledger.observationBill input.fees + P.experiment.observationCharge reviews := by
    exact (congrArg (fun state : State P.sharedInstance => state.ledger.observationBill input.fees) hrNext).trans
      ((menuRepairedFrom_observationBill_exact accounting stage written tool input.fees).trans hobs)
  obtain ⟨ended, hended, hhalt, hoChild, hTraceChild, hsChild⟩ := ih nextclock hentryNext'
  rw [hkNext] at hoChild hTraceChild hsChild
  have hoChild' : (run input C .uncapped accounting rule sample ended).ledger.observationBill input.fees =
      (run input C .uncapped accounting rule sample nextclock).ledger.observationBill input.fees + child.observation := hoChild
  have hsChild' : runSuccess input C .uncapped accounting rule sample ↔ child.failure = false := hsChild
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
  have hk : k ≠ 0 := Nat.ne_zero_of_lt hpos
  have hsummary : pathSummary P (calibratedFamily P) table (n + 1) k
      (calibratedSuffixSeed P cursor (n + 1) hfit sample.1)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2) =
        { observation := P.experiment.observationCharge reviews + child.observation,
          trace := (true, true) :: child.trace, failure := child.failure } := by
    have hs := pathSummary_test_repair P (calibratedFamily P) table n k level reviews
      (calibratedStageTest P level)
      (calibratedSuffixSeed P cursor (n + 1) hfit sample.1)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2) ha
      (calibratedFamily_some P level valid) hstopCrop hwrongCrop hk
    rw [calibratedSuffixSeed_tail P cursor n hfit hnextfit,
      menuSuffixWorld_tail P P.certificate.stages P.tools cursor n hfit hnextfit fee hfee sample.2] at hs
    exact hs
  have hlegal := menuRule_legal P table fee hfee C hC.1.1 accounting
  have hpacket : written = menuWrittenFrom input C accounting stage start
      (worldTapes input sample.2 stage) reviews bit :=
    menuEntry_run_written P table fee hfee C hC.1.1 accounting sample cursor n clock hfit
      stage hstage hentry level reviews .repair valid ha hstop
  have hUsedWritten : historyUsed written.history = historyUsed start.history := by
    rw [hpacket]
    exact menuWrittenFrom_used input C hC.1.1 accounting stage start _ reviews _
  have hUsedNext : historyUsed (run input C .uncapped accounting rule sample nextclock).history =
      insert tool (historyUsed start.history) := by
    exact (congrArg (fun state : State P.sharedInstance => historyUsed state.history) hrNext).trans
      ((menuRepairedFrom_used accounting stage written tool).trans
        (congrArg (fun used : Finset P.sharedInstance.Tool =>
          insert (show P.sharedInstance.Tool from tool) used) hUsedWritten))
  have hPairsNext : executionPairs P (run input C .uncapped accounting rule sample nextclock).ledger =
      executionPairs P start.ledger ++ [(cursor, tool)] := by
    rw [hrNext, menuRepairedFrom_pairs]
    unfold executionPairs
    rw [hexecutions, hstage]
  have hFindDecode : unusedTool P.tools (historyUsed start.history) = some tool := by
    have h : unusedTool P.tools (historyUsed written.history) = some tool := hfind
    rw [hUsedWritten] at h
    exact h
  have hTraceChild' : TraceLedgerMatch P (cursor + 1) (insert tool (historyUsed start.history)) child.trace
      (run input C .uncapped accounting rule sample nextclock) (run input C .uncapped accounting rule sample ended) := by
    rw [hUsedNext] at hTraceChild
    exact hTraceChild
  have hwriteEnd : (run input C .uncapped accounting rule sample ended).ledger.written stage =
      some (!(input.truthAt sample.2 stage)) := by
    apply run_written_at_later input C .uncapped accounting rule hlegal sample writeclock ended
      (by dsimp only [nextclock] at hended; omega) stage _
    exact hwritten.trans (congrArg some (Bool.eq_not_iff.mpr hwrong))
  have hhead : ∀ other : P.sharedInstance.Stage, other.val = cursor →
      (run input C .uncapped accounting rule sample ended).ledger.written other =
        some (!((run input C .uncapped accounting rule sample ended).ledger.truth other)) := by
    intro other ho
    have heq : other = stage := Fin.ext (ho.trans hstage.symm)
    subst other
    rw [run_truth input C .uncapped accounting rule hlegal sample ended]
    exact hwriteEnd
  have hTrace : TraceLedgerMatch P cursor (historyUsed start.history) ((true, true) :: child.trace)
      start (run input C .uncapped accounting rule sample ended) :=
    traceLedgerMatch_cons_repair P cursor (historyUsed start.history) tool child.trace start
      (run input C .uncapped accounting rule sample nextclock) _ hhead hFindDecode hPairsNext hTraceChild'
  unfold EntryRecords
  dsimp only
  rw [hsummary]
  refine ⟨ended, (by dsimp only [nextclock, writeclock] at hended; omega), hhalt, ?_, hTrace, hsChild'⟩
  · calc
      _ = (run input C .uncapped accounting rule sample nextclock).ledger.observationBill input.fees + child.observation := hoChild'
      _ = (start.ledger.observationBill input.fees + P.experiment.observationCharge reviews) + child.observation :=
        congrArg (fun charge => charge + child.observation) hoNext
      _ = _ := add_assoc _ _ _


end PDROC.CalibratedRuntime
