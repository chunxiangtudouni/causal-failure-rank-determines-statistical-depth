module

public import PaperProofs.Paid.PDROC_CalibratedIdeal_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu PDROC.CalibratedRuntime

namespace PDROC.CalibratedIdeal

theorem entryTrace_test_abort (P : Parameters) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = P.certificate.stages)
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
    (hwrong : (menuAnalysisTest P level).rule.decision (sample.1 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage
        (worldTapes (P.input fee hfee) sample.2 stage)) ≠ (P.input fee hfee).truthAt sample.2 stage)
    (habort : bad = .abandon ∨ P.tools - (run (P.input fee hfee) C.val .uncapped accounting
      (P.compiledMenuRule P.certificate.stages P.tools table) sample clock).ledger.executions.length = 0) :
    EntryTrace P table fee hfee C accounting sample cursor (n + 1) clock hfit := by
  let input := P.input fee hfee
  let rule := P.compiledMenuRule P.certificate.stages P.tools table
  let start := run input C.val .uncapped accounting rule sample clock
  let k := P.tools - start.ledger.executions.length
  let writeclock := clock + reviews + 1
  let ended := clock + reviews + 2
  have legal := P.compiledMenuRule_uncapped_legal P.certificate.stages P.tools table fee hfee C.val C.property.1.1 accounting
  have aborted := PDROC.menuEntry_test_abort_run P P.certificate.stages P.tools table fee hfee C.val C.property accounting
    sample cursor n clock hfit stage hstage hentry level reviews bad ha hstop hwrong habort
  have write := menuEntry_run_written P P.certificate.stages P.tools table fee hfee C.val C.property.1.1 accounting sample
    cursor n clock hfit stage hstage hentry level reviews bad ha hstop
  obtain ⟨_, _, hw, _, _, he, _, _, _⟩ := menuEntry_written_records P P.certificate.stages P.tools table fee hfee
    C.val C.property accounting sample cursor n clock hfit stage hstage hentry level reviews bad ha hstop
  have abortState : run input C.val .uncapped accounting rule sample ended =
      stopState (run input C.val .uncapped accounting rule sample writeclock) true := aborted
  have writeState : run input C.val .uncapped accounting rule sample writeclock =
      menuWrittenFrom input C.val accounting stage start (worldTapes input sample.2 stage) reviews
        ((menuAnalysisTest P level).rule.decision (sample.1 stage)
          (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes input sample.2 stage))) := write
  have executionsWritten : (run input C.val .uncapped accounting rule sample writeclock).ledger.executions =
      start.ledger.executions := he
  obtain ⟨_, fresh⟩ := firstEntryAt_unborn input C.val .uncapped accounting rule legal sample cursor clock hentry
  have pairEnd : executionPairs P (run input C.val .uncapped accounting rule sample ended).ledger =
      executionPairs P start.ledger := by
    rw [abortState]
    change executionPairs P (run input C.val .uncapped accounting rule sample writeclock).ledger = _
    simp only [executionPairs, executionsWritten]
  have tailMatch : TraceLedgerMatch P (cursor + 1) (historyUsed start.history) [] start
      (run input C.val .uncapped accounting rule sample ended) := by
    apply traceLedgerMatch_nil P (cursor + 1) (historyUsed start.history) start _ _ pairEnd
    intro other hs
    have hne : other ≠ stage := fun h => by subst other; omega
    rw [abortState]
    change (run input C.val .uncapped accounting rule sample writeclock).ledger.written other = none
    rw [writeState, menuWrittenFrom_other input C.val accounting stage other start _ reviews _ hne]
    exact (fresh other (by omega)).1
  have seedHead := menuSuffixSeed_head P.certificate.stages P.tools cursor n hfit sample.1 stage hstage
  have worldHead := menuSuffixWorld_head P P.certificate.stages P.tools cursor n hfit fee hfee sample.2 stage hstage
  have stopCrop : (menuAnalysisTest P level).rule.stop
      (menuSuffixSeed P.certificate.stages P.tools cursor (n + 1) hfit sample.1 0)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2 0).2 = reviews := by
    rw [seedHead, worldHead]
    exact hstop
  have wrongCrop : (menuAnalysisTest P level).rule.decision
      (menuSuffixSeed P.certificate.stages P.tools cursor (n + 1) hfit sample.1 0)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2 0).2 ≠
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2 0).1 := by
    rw [seedHead, worldHead]
    exact hwrong
  have summary : pathSummary P (idealFamily P) table (n + 1) k
      (menuSuffixSeed P.certificate.stages P.tools cursor (n + 1) hfit sample.1)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2) =
      {observation := P.experiment.observationCharge reviews, trace := [(true, false)], failure := true} := by
    cases bad with
    | abandon =>
        exact pathSummary_test_abandon P (idealFamily P) table n k level reviews (menuAnalysisTest P level)
          _ _ ha rfl stopCrop wrongCrop
    | repair =>
        have zero : k = 0 := habort.resolve_left (by decide)
        rw [zero]
        have haZero : (menuEntryAt table (n + 1) 0).action = .test level .repair := by rw [← zero]; exact ha
        exact pathSummary_test_no_tool P (idealFamily P) table n level reviews (menuAnalysisTest P level)
          _ _ haZero rfl stopCrop wrongCrop
  unfold EntryTrace
  dsimp only
  rw [summary]
  refine ⟨ended, (by dsimp only [ended]; omega), ?_, ?_⟩
  · rw [abortState]
    rfl
  · apply traceLedgerMatch_cons_noRepair P cursor (historyUsed start.history) true [] start start _ _ rfl tailMatch
    intro other ho
    have same : other = stage := Fin.ext (ho.trans hstage.symm)
    subst other
    change (run input C.val .uncapped accounting rule sample ended).ledger.written stage =
      some (!(run input C.val .uncapped accounting rule sample ended).ledger.truth stage)
    rw [run_truth input C.val .uncapped accounting rule legal sample ended]
    exact written_of_clock_le input C.val .uncapped accounting rule legal sample writeclock ended
      (by dsimp only [writeclock, ended]; omega) stage _ (hw.trans (congrArg some (bool_ne_eq_not _ _ hwrong)))

end PDROC.CalibratedIdeal
