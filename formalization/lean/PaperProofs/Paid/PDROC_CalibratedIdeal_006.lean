module

public import PaperProofs.Paid.PDROC_CalibratedIdeal_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu PDROC.CalibratedRuntime

namespace PDROC.CalibratedIdeal

theorem entryTrace_repair (P : Parameters) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = P.certificate.stages)
    (hnextfit : cursor + 1 + n = P.certificate.stages)
    (stage : P.sharedInstance.Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
      (P.compiledMenuRule P.certificate.stages P.tools table) cursor clock sample)
    (level reviews : ℕ)
    (ha : (menuEntryAt table (n + 1)
      (P.tools - (run (P.input fee hfee) C.val .uncapped accounting
        (P.compiledMenuRule P.certificate.stages P.tools table) sample clock).ledger.executions.length)).action = .test level .repair)
    (hstop : (menuAnalysisTest P level).rule.stop (sample.1 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage
        (worldTapes (P.input fee hfee) sample.2 stage)) = reviews)
    (hwrong : (menuAnalysisTest P level).rule.decision (sample.1 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage
        (worldTapes (P.input fee hfee) sample.2 stage)) ≠ (P.input fee hfee).truthAt sample.2 stage)
    (hpositive : 0 < P.tools - (run (P.input fee hfee) C.val .uncapped accounting
      (P.compiledMenuRule P.certificate.stages P.tools table) sample clock).ledger.executions.length)
    (ih : ∀ nextclock, FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
      (P.compiledMenuRule P.certificate.stages P.tools table) (cursor + 1) nextclock sample →
      EntryTrace P table fee hfee C accounting sample (cursor + 1) n nextclock hnextfit) :
    EntryTrace P table fee hfee C accounting sample cursor (n + 1) clock hfit := by
  let input := P.input fee hfee
  let rule := P.compiledMenuRule P.certificate.stages P.tools table
  let start := run input C.val .uncapped accounting rule sample clock
  let writeclock := clock + reviews + 1
  let written := run input C.val .uncapped accounting rule sample writeclock
  let nextclock := writeclock + 3
  let middle := run input C.val .uncapped accounting rule sample nextclock
  let k := P.tools - start.ledger.executions.length
  let child := pathSummary P (idealFamily P) table n (k - 1)
    (menuSuffixSeed P.certificate.stages P.tools (cursor + 1) n hnextfit sample.1)
    (menuSuffixWorld P P.certificate.stages P.tools (cursor + 1) n hnextfit fee hfee sample.2)
  have legal := P.compiledMenuRule_uncapped_legal P.certificate.stages P.tools table fee hfee C.val C.property.1.1 accounting
  obtain ⟨active, hc, hw, ht, _, he, htools, havailable, hnoCurrent⟩ :=
    menuEntry_written_records P P.certificate.stages P.tools table fee hfee C.val C.property accounting sample
      cursor n clock hfit stage hstage hentry level reviews .repair ha hstop
  have hcStage : written.cursor = stage.val := hc.trans hstage.symm
  have wrongWritten : (menuAnalysisTest P level).rule.decision (sample.1 stage)
      (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes input sample.2 stage)) ≠
      written.ledger.truth stage := by
    have truthWritten : written.ledger.truth = input.truthAt sample.2 := ht
    rw [truthWritten]
    exact hwrong
  have row : P.certificate.stages - stage.val = n + 1 := by omega
  have toolsWritten : P.menuEntryTools P.certificate.stages P.tools written.history stage = k := htools
  have availableWritten : (Finset.univ \ historyUsed written.history).card = k := havailable
  have executionsWritten : written.ledger.executions = start.ledger.executions := he
  have cell : (menuEntryAt table (P.certificate.stages - stage.val)
      (P.menuEntryTools P.certificate.stages P.tools written.history stage)).action = .test level .repair := by
    rw [row, toolsWritten]
    exact ha
  have available : 0 < (Finset.univ \ historyUsed written.history).card := by rw [availableWritten]; exact hpositive
  obtain ⟨selectedTool, find, _, _, advanced, entryNext⟩ := ideal_repair_threeSteps_with_choice P P.certificate.stages P.tools
    table fee hfee C.val C.property.1.1 accounting sample stage writeclock _ level active hcStage hw wrongWritten
      cell hnoCurrent available
  let tool : Fin P.tools := selectedTool
  have repaired : middle = menuRepairedFrom accounting stage written tool := advanced
  have entryNext' : FirstEntryAt input C.val .uncapped accounting rule (cursor + 1) nextclock sample := by
    rw [hstage] at entryNext
    exact entryNext
  have countNext : P.tools - middle.ledger.executions.length = k - 1 := by
    rw [repaired, menuRepairedFrom_executionCount accounting stage written tool, executionsWritten]
    exact Nat.sub_add_eq _ _ _
  have usedWritten : historyUsed written.history = historyUsed start.history := by
    have writeState : written = menuWrittenFrom input C.val accounting stage start
        (worldTapes input sample.2 stage) reviews
        ((menuAnalysisTest P level).rule.decision (sample.1 stage)
          (menuOriginalTape P P.certificate.stages P.tools fee hfee stage (worldTapes input sample.2 stage))) :=
      menuEntry_run_written P P.certificate.stages P.tools table fee hfee C.val C.property.1.1 accounting sample
        cursor n clock hfit stage hstage hentry level reviews .repair ha hstop
    rw [writeState]
    exact menuWrittenFrom_used input C.val C.property.1.1 accounting stage start _ reviews _
  have usedNext : historyUsed middle.history = insert tool (historyUsed start.history) := by
    rw [repaired, menuRepairedFrom_used accounting stage written tool, usedWritten]
    with_unfolding_all rfl
  have find' : unusedTool P.tools (historyUsed start.history) = some tool := by
    change unusedTool P.tools (historyUsed written.history) = some tool at find
    rw [usedWritten] at find
    exact find
  have pairNext : executionPairs P middle.ledger = executionPairs P start.ledger ++ [(cursor, tool)] := by
    rw [repaired, executionPairs_repaired P accounting stage written tool, hstage]
    simp only [executionPairs, executionsWritten]
  obtain ⟨ended, order, halted, matched⟩ := ih nextclock entryNext'
  rw [countNext, usedNext] at matched
  have childMatch : TraceLedgerMatch P (cursor + 1) (insert tool (historyUsed start.history)) child.trace middle
      (run input C.val .uncapped accounting rule sample ended) := matched
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
      {observation := P.experiment.observationCharge reviews + child.observation,
        trace := (true, true) :: child.trace, failure := child.failure} := by
    have h := pathSummary_test_repair P (idealFamily P) table n k level reviews (menuAnalysisTest P level)
      (menuSuffixSeed P.certificate.stages P.tools cursor (n + 1) hfit sample.1)
      (menuSuffixWorld P P.certificate.stages P.tools cursor (n + 1) hfit fee hfee sample.2) ha rfl stopCrop wrongCrop
        (Nat.ne_of_gt hpositive)
    rw [menuSuffixSeed_tail P.certificate.stages P.tools cursor n hfit hnextfit sample.1,
      menuSuffixWorld_tail P P.certificate.stages P.tools cursor n hfit hnextfit fee hfee sample.2] at h
    exact h
  unfold EntryTrace
  dsimp only
  rw [summary]
  refine ⟨ended, (by dsimp only [nextclock, writeclock] at order; omega), halted, ?_⟩
  apply traceLedgerMatch_cons_repair P cursor (historyUsed start.history) tool child.trace start middle _ _ find' pairNext childMatch
  intro other ho
  have same : other = stage := Fin.ext (ho.trans hstage.symm)
  subst other
  rw [run_truth input C.val .uncapped accounting rule legal sample ended]
  exact written_of_clock_le input C.val .uncapped accounting rule legal sample writeclock ended
    (by dsimp only [nextclock, writeclock] at order; omega) stage _ (hw.trans (congrArg some (bool_ne_eq_not _ _ hwrong)))

end PDROC.CalibratedIdeal
