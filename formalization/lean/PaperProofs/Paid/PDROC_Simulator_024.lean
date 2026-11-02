module

public import PaperProofs.Paid.PDROC_Simulator_023

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem simulatorReplay_append_marks_nonwrite {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (event : VisibleEvent I)
    (hm : markedHistory history = markedHistory (simulatorReplay draw seed history).shadow)
    (hw : ∀ stage, eventWrite stage event = none) (hr : ∀ stage, eventReport stage event = none) :
    markedHistory (history ++ [event]) = markedHistory (simulatorReplay draw seed (history ++ [event])).shadow := by
  have hi : markedHistory (simulatorReplay draw seed history).seen =
      markedHistory (simulatorReplay draw seed history).shadow := by
    simpa only [simulatorReplay_seen] using hm
  have hn := simulatorStep_marks_nonwrite draw seed (simulatorReplay draw seed history) event hi hw hr
  rw [simulatorStep_seen, simulatorReplay_seen] at hn
  simpa only [simulatorReplay, List.foldl_append, List.foldl_cons, List.foldl_nil] using hn

/-- Exact marks on every genuine early-report prefix, including abandonment.
The virtual cache need not be a separate Native execution. -/
theorem simulatorReplay_markedHistory_prefix {SimSeed : Type*} {ActualSeed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (actual : PolicyRule I ActualSeed) (actualSeed : ActualSeed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting actual actualSeed truth tapes n s)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I)) (seed : SimSeed) :
    markedHistory s.history = markedHistory (simulatorReplay draw seed s.history).shadow := by
  induction hp with
  | initial => rfl
  | @next n before after hp hs ih =>
    generalize haction : actual actualSeed before.history = action at hs
    cases hs with
    | write stage bit live port resources =>
      have hreport : historyReport before.history stage = none := by
        rw [prefix_historyReport_early input C hearly mode accounting actual actualSeed truth tapes hp]
        have hinv := prefix_invariant input C mode accounting actual actualSeed truth tapes hp
        cases ht : before.ledger.reportTime stage with
        | none => rfl
        | some time => exact (hinv.report_written stage time ht port).elim
      have hi : markedHistory (simulatorReplay draw seed before.history).seen =
          markedHistory (simulatorReplay draw seed before.history).shadow := by
        simpa only [simulatorReplay_seen] using ih
      have ha : historyReport (simulatorReplay draw seed before.history).seen stage = none := by
        simpa only [simulatorReplay_seen] using hreport
      have hv := simulatorReplay_report_none draw seed before.history stage hreport
      have hn := simulatorStep_writeReport_marks draw seed (simulatorReplay draw seed before.history)
        stage bit (before.ledger.truth stage) before.clock hi ha hv
      dsimp only at hn
      rw [simulatorStep_seen, simulatorStep_seen, simulatorReplay_seen] at hn
      simpa only [record, writeResponses, hearly, ↓reduceIte, writeLedger, List.singleton_append,
        simulatorReplay, List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_assoc] using hn
    | review stage live port resources =>
      exact simulatorReplay_append_marks_nonwrite draw seed before.history _ ih (fun _ => rfl) (fun _ => rfl)
    | allocate handle tool active valid compatible unused unallocated window resources =>
      exact simulatorReplay_append_marks_nonwrite draw seed before.history _ ih (fun _ => rfl) (fun _ => rfl)
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      exact simulatorReplay_append_marks_nonwrite draw seed before.history _ ih (fun _ => rfl) (fun _ => rfl)
    | advance stage live written resources =>
      exact simulatorReplay_append_marks_nonwrite draw seed before.history _ ih (fun _ => rfl) (fun _ => rfl)
    | stop active =>
      exact simulatorReplay_append_marks_nonwrite draw seed before.history _ ih (fun _ => rfl) (fun _ => rfl)
    | abandon active =>
      exact simulatorReplay_append_marks_nonwrite draw seed before.history _ ih (fun _ => rfl) (fun _ => rfl)

end PDROC
