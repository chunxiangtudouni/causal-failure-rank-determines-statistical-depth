module

public import PaperProofs.Paid.PDROC_CalibratedIdeal_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu PDROC.CalibratedRuntime

namespace PDROC.CalibratedIdeal

theorem written_of_clock_le {I : Instance} {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (legal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (start ended : ℕ) (order : start ≤ ended) (stage : I.Stage) (bit : Bool)
    (written : (run input C mode accounting rule sample start).ledger.written stage = some bit) :
    (run input C mode accounting rule sample ended).ledger.written stage = some bit := by
  have h := run_written_some_after input C mode accounting rule legal sample start (ended - start) stage bit written
  simpa only [Nat.add_sub_of_le order] using h

theorem entryTrace_correct (P : Parameters) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = P.certificate.stages)
    (hnextfit : cursor + 1 + n = P.certificate.stages)
    (stage : P.sharedInstance.Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
      (P.compiledMenuRule P.certificate.stages P.tools table) cursor clock sample)
    (level reviews : ℕ) (bad : MenuBadAction)
    (ha : (menuEntryAt table (n + 1)
      (P.tools - (run (P.input fee hfee) C.val .uncapped accounting
        (P.compiledMenuRule P.certificate.stages P.tools table) sample clock).ledger.executions.length)).action = .test level bad)
    (hstop : (menuAnalysisTest P level).rule.stop (sample.1 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage
        (worldTapes (P.input fee hfee) sample.2 stage)) = reviews)
    (hcorrect : (menuAnalysisTest P level).rule.decision (sample.1 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage
        (worldTapes (P.input fee hfee) sample.2 stage)) = (P.input fee hfee).truthAt sample.2 stage)
    (ih : ∀ nextclock, FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
      (P.compiledMenuRule P.certificate.stages P.tools table) (cursor + 1) nextclock sample →
      EntryTrace P table fee hfee C accounting sample (cursor + 1) n nextclock hnextfit) :
    EntryTrace P table fee hfee C accounting sample cursor (n + 1) clock hfit := by
  let input := P.input fee hfee
  let rule := P.compiledMenuRule P.certificate.stages P.tools table
  let start := run input C.val .uncapped accounting rule sample clock
  let writeclock := clock + reviews + 1
  let written := run input C.val .uncapped accounting rule sample writeclock
  let nextclock := writeclock + 1
  let middle := run input C.val .uncapped accounting rule sample nextclock
  let k := P.tools - start.ledger.executions.length
  let child := pathSummary P (idealFamily P) table n k
    (menuSuffixSeed P.certificate.stages P.tools (cursor + 1) n hnextfit sample.1)
    (menuSuffixWorld P P.certificate.stages P.tools (cursor + 1) n hnextfit fee hfee sample.2)
  have legal := P.compiledMenuRule_uncapped_legal P.certificate.stages P.tools table fee hfee C.val C.property.1.1 accounting
  obtain ⟨active, hc, hw, ht, _, he, _, _, _⟩ := menuEntry_written_records P P.certificate.stages P.tools table fee hfee
    C.val C.property accounting sample cursor n clock hfit stage hstage hentry level reviews bad ha hstop
  have hcStage : written.cursor = stage.val := hc.trans hstage.symm
  have good : written.ledger.written stage = some (written.ledger.truth stage) :=
    hw.trans (congrArg some (hcorrect.trans (congrFun ht stage).symm))
  have advanced := compiledMenu_run_correct_advance P P.certificate.stages P.tools table fee hfee C.val C.property.1.1
    accounting sample stage writeclock active hcStage good
  have advancedState : middle = record accounting written (.advance stage) [.advanced stage]
      (advanceLedger written stage) (written.cursor + 1) false := advanced
  have cursorNext : middle.cursor = cursor + 1 := by
    rw [advancedState]
    exact congrArg (fun value : ℕ => value + 1) hc
  have entryNext := menuFirstEntryAfterAdvance input C.val .uncapped accounting rule legal sample writeclock cursor hc cursorNext
  have executionNext : middle.ledger.executions = start.ledger.executions := by
    rw [advancedState]
    exact he
  have countNext := congrArg List.length executionNext
  have usedWritten : historyUsed written.history = historyUsed start.history := by
    have writeState : written = menuWrittenFrom input C.val accounting stage start
        (worldTapes input sample.2 stage) reviews
        ((menuAnalysisTest P level).rule.decision (sample.1 stage)
          (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes input sample.2 stage))) :=
      menuEntry_run_written P P.certificate.stages P.tools table fee hfee C.val C.property.1.1 accounting sample
        cursor n clock hfit stage hstage hentry level reviews bad ha hstop
    rw [writeState]
    exact menuWrittenFrom_used input C.val C.property.1.1 accounting stage start _ reviews _
  have usedNext : historyUsed middle.history = historyUsed start.history := by
    rw [advancedState, advance_used, usedWritten]
  obtain ⟨ended, order, halted, matched⟩ := ih nextclock entryNext
  rw [countNext, usedNext] at matched
  have childMatch : TraceLedgerMatch P (cursor + 1) (historyUsed start.history) child.trace middle
      (run input C.val .uncapped accounting rule sample ended) := matched
  have seedHead := menuSuffixSeed_head P.certificate.stages P.tools cursor n hfit sample.1 stage hstage
  have worldHead := menuSuffixWorld_head P P.certificate.stages P.tools cursor n hfit fee hfee sample.2 stage hstage
  have stopCrop : (menuAnalysisTest P level).rule.stop
      (menuSuffixSeed P.certificate.stages P.tools cursor (n + 1) hfit sample.1 0)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2 0).2 = reviews := by
    rw [seedHead, worldHead]
    exact hstop
  have correctCrop : (menuAnalysisTest P level).rule.decision
      (menuSuffixSeed P.certificate.stages P.tools cursor (n + 1) hfit sample.1 0)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2 0).2 =
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2 0).1 := by
    rw [seedHead, worldHead]
    exact hcorrect
  have summary : pathSummary P (idealFamily P) table (n + 1) k
      (menuSuffixSeed P.certificate.stages P.tools cursor (n + 1) hfit sample.1)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2) =
      {observation := P.experiment.observationCharge reviews + child.observation,
        trace := (false, false) :: child.trace, failure := child.failure} := by
    have h := pathSummary_test_correct P (idealFamily P) table n k level reviews bad (menuAnalysisTest P level)
      (menuSuffixSeed P.certificate.stages P.tools cursor (n + 1) hfit sample.1)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2) ha rfl stopCrop correctCrop
    rw [menuSuffixSeed_tail P.certificate.stages P.tools cursor n hfit hnextfit sample.1,
      menuSuffixWorld_tail P P.certificate.stages P.tools cursor n hfit hnextfit fee hfee sample.2] at h
    exact h
  unfold EntryTrace
  dsimp only
  rw [summary]
  refine ⟨ended, (by dsimp only [nextclock, writeclock] at order; omega), halted, ?_⟩
  apply traceLedgerMatch_cons_noRepair P cursor (historyUsed start.history) false child.trace start middle _
  · intro other ho
    have same : other = stage := Fin.ext (ho.trans hstage.symm)
    subst other
    change (run input C.val .uncapped accounting rule sample ended).ledger.written stage =
      some ((run input C.val .uncapped accounting rule sample ended).ledger.truth stage)
    rw [run_truth input C.val .uncapped accounting rule legal sample ended]
    exact written_of_clock_le input C.val .uncapped accounting rule legal sample writeclock ended
      (by dsimp only [nextclock] at order; omega) stage _ (hw.trans (congrArg some hcorrect))
  · simp only [executionPairs, executionNext]
  · exact childMatch

end PDROC.CalibratedIdeal
