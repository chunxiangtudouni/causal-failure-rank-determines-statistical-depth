module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_009
public import PaperProofs.Paid.PDROC_CalibratedRuntime_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu

namespace PDROC.CalibratedRuntime

theorem entryRecords_test_correct (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedMenuSeed × (P.input fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = P.certificate.stages) (hnextfit : cursor + 1 + n = P.certificate.stages)
    (stage : P.sharedInstance.Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.input fee hfee) C .uncapped accounting
      (menuRule P table) cursor clock sample)
    (level reviews : ℕ) (bad : MenuBadAction) (valid : level ≤ P.certificate.M)
    (ha : (Parameters.menuEntryAt table (n + 1)
      (P.tools - (run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.executions.length)).action = .test level bad)
    (hstop : (calibratedStageTest P level).rule.stop (sample.1.1 stage, sample.1.2 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes (P.input fee hfee) sample.2 stage)) = reviews)
    (hcorrect : (calibratedStageTest P level).rule.decision (sample.1.1 stage, sample.1.2 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes (P.input fee hfee) sample.2 stage)) =
        (P.input fee hfee).truthAt sample.2 stage)
    (ih : ∀ nextclock, FirstEntryAt (P.input fee hfee) C .uncapped accounting
      (menuRule P table) (cursor + 1) nextclock sample →
        EntryRecords P table fee hfee C accounting sample (cursor + 1) n nextclock hnextfit) :
    EntryRecords P table fee hfee C accounting sample cursor (n + 1) clock hfit := by
  let input := P.input fee hfee
  let rule := menuRule P table
  let start := run input C .uncapped accounting rule sample clock
  let writeclock := clock + reviews + 1
  let written := run input C .uncapped accounting rule sample writeclock
  let nextclock := writeclock + 1
  let k := P.tools - start.ledger.executions.length
  let child := pathSummary P (calibratedFamily P) table n k
    (calibratedSuffixSeed P (cursor + 1) n hnextfit sample.1)
    (menuSuffixWorld P P.certificate.stages P.tools (cursor + 1) n hnextfit fee hfee sample.2)
  have hlegal := menuRule_legal P table fee hfee C hC.1.1 accounting
  obtain ⟨hactive, hcursor, hwritten, htruth, hobs, hexecutions, _, _, _⟩ :=
    menuEntry_written_records P table fee hfee C hC accounting sample cursor n clock hfit stage hstage
      hentry level reviews bad valid ha hstop
  have hcStage : written.cursor = stage.val := hcursor.trans hstage.symm
  replace hexecutions : written.ledger.executions = start.ledger.executions := hexecutions
  have hgood : written.ledger.written stage = some (written.ledger.truth stage) :=
    hwritten.trans (congrArg some (hcorrect.trans (congrFun htruth stage).symm))
  have hadv : run input C .uncapped accounting rule sample nextclock =
      record accounting written (.advance stage) [.advanced stage]
        (advanceLedger written stage) (written.cursor + 1) false :=
    menu_run_correct_advance P table fee hfee C hC.1.1 accounting
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
  obtain ⟨ended, hended, hhalt, hoChild, hTraceChild, hsChild⟩ := ih nextclock hentryNext
  rw [heNext] at hoChild hTraceChild hsChild
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
  have hcorrectCrop : (calibratedStageTest P level).rule.decision
      (calibratedSuffixSeed P cursor (n + 1) hfit sample.1 0)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2 0).2 =
        (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2 0).1 := by
    rw [hseed, hworld]
    exact hcorrect
  have hsummary : pathSummary P (calibratedFamily P) table (n + 1) k
      (calibratedSuffixSeed P cursor (n + 1) hfit sample.1)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2) =
        { observation := P.experiment.observationCharge reviews + child.observation,
          trace := (false, false) :: child.trace, failure := child.failure } := by
    have hs := pathSummary_test_correct P (calibratedFamily P) table n k level reviews bad
      (calibratedStageTest P level)
      (calibratedSuffixSeed P cursor (n + 1) hfit sample.1)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2) ha
      (calibratedFamily_some P level valid) hstopCrop hcorrectCrop
    rw [calibratedSuffixSeed_tail P cursor n hfit hnextfit,
      menuSuffixWorld_tail P P.certificate.stages P.tools cursor n hfit hnextfit fee hfee sample.2] at hs
    exact hs
  have hpacket : written = menuWrittenFrom input C accounting stage start
      (worldTapes input sample.2 stage) reviews
      ((calibratedStageTest P level).rule.decision (sample.1.1 stage, sample.1.2 stage)
        (worldTapes input sample.2 stage)) :=
    menuEntry_run_written P table fee hfee C hC.1.1 accounting sample cursor n clock hfit
      stage hstage hentry level reviews bad valid ha hstop
  have hUsedWritten : historyUsed written.history = historyUsed start.history := by
    rw [hpacket]
    exact menuWrittenFrom_used input C hC.1.1 accounting stage start _ reviews _
  have hUsedNext : historyUsed (run input C .uncapped accounting rule sample nextclock).history =
      historyUsed start.history := by
    rw [hadv, advanceRecord_used]
    exact hUsedWritten
  have hPairsNext : executionPairs P (run input C .uncapped accounting rule sample nextclock).ledger =
      executionPairs P start.ledger := by
    rw [hadv, advanceRecord_pairs]
    unfold executionPairs
    rw [hexecutions]
  have hTraceChild' : TraceLedgerMatch P (cursor + 1) (historyUsed start.history) child.trace
      (run input C .uncapped accounting rule sample nextclock) (run input C .uncapped accounting rule sample ended) := by
    rw [hUsedNext] at hTraceChild
    exact hTraceChild
  have hwriteEnd : (run input C .uncapped accounting rule sample ended).ledger.written stage =
      some (input.truthAt sample.2 stage) := by
    apply run_written_at_later input C .uncapped accounting rule hlegal sample writeclock ended
      (by dsimp only [nextclock] at hended; omega) stage _
    exact hwritten.trans (congrArg some hcorrect)
  have hhead : ∀ other : P.sharedInstance.Stage, other.val = cursor →
      (run input C .uncapped accounting rule sample ended).ledger.written other =
        some ((run input C .uncapped accounting rule sample ended).ledger.truth other) := by
    intro other ho
    have heq : other = stage := Fin.ext (ho.trans hstage.symm)
    subst other
    rw [run_truth input C .uncapped accounting rule hlegal sample ended]
    exact hwriteEnd
  have hTrace : TraceLedgerMatch P cursor (historyUsed start.history) ((false, false) :: child.trace)
      start (run input C .uncapped accounting rule sample ended) :=
    traceLedgerMatch_cons_noRepair P cursor (historyUsed start.history) false child.trace start
      (run input C .uncapped accounting rule sample nextclock) _ hhead hPairsNext hTraceChild'
  unfold EntryRecords
  dsimp only
  rw [hsummary]
  refine ⟨ended, (by dsimp only [nextclock, writeclock] at hended; omega), hhalt, ?_, hTrace, hsChild'⟩
  calc
    _ = (run input C .uncapped accounting rule sample nextclock).ledger.observationBill input.fees + child.observation := hoChild'
    _ = (start.ledger.observationBill input.fees + P.experiment.observationCharge reviews) + child.observation :=
      congrArg (fun charge => charge + child.observation) hoNext
    _ = _ := add_assoc _ _ _


end PDROC.CalibratedRuntime
