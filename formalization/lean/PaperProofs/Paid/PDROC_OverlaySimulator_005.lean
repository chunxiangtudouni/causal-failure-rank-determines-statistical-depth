module

public import PaperProofs.Paid.PDROC_OverlaySimulator_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {SimSeed : Type u}

theorem overlayReplay_append_event
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (event : VisibleEvent I) :
    overlayReplay draw mark ghost seed (history ++ [event]) =
      overlayStep draw mark ghost seed (overlayReplay draw mark ghost seed history) event := by
  simp only [overlayReplay, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem overlayStep_report_frame
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) (stage : I.Stage)
    (he : eventReport stage event = none) :
    historyReport (overlayStep draw mark ghost seed cache event).shadow stage = historyReport cache.shadow stage := by
  cases event with
  | observation | wrote | committed | executed | advanced | stopped | abandoned =>
    simp only [overlayStep, simulatorStep, simulatorAppend]
    all_goals (try split_ifs)
    all_goals simp [historyReport, overlayGhostEvents_no_report, simulatorReviewPacket,
      List.filterMap_append, List.filterMap_map, Function.comp_def, eventReport]
  | report current truth serial =>
    have hne : current ≠ stage := by intro h; subst current; simp [eventReport] at he
    simp [overlayStep, simulatorAppend, historyReport, List.filterMap_append, eventReport, hne]

/-- Exact post-report truth and serial for the chosen writing record. Neither
the auxiliary old decision nor a virtual-only mark causes an earlier report. -/
theorem overlayReplay_writeReport_report
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage)
    (bit truth : Bool) (serial : ℕ) (decision : Bool)
    (hd : (simulatorDrawRecord (draw seed stage (overlayReplay draw mark ghost seed history).shadow)).decision =
      some decision) :
    let record := simulatorDrawRecord (draw seed stage (overlayReplay draw mark ghost seed history).shadow)
    historyReport (overlayReplay draw mark ghost seed
      (history ++ [.wrote stage bit serial, .report stage truth serial])).shadow stage =
      some (overlayReportTruth bit decision truth (mark seed stage record),
        (historyActions (overlayReplay draw mark ghost seed history).shadow).length + record.observations.length) := by
  dsimp only
  rw [show history ++ [.wrote stage bit serial, .report stage truth serial] =
    (history ++ [.wrote stage bit serial]) ++ [.report stage truth serial] by simp]
  rw [overlayReplay_append_event, overlayReplay_append_event]
  simp only [overlayStep, simulatorStep, simulatorAppend, Function.update_self, Option.getD_some]
  rw [hd]
  simp only [Option.getD_some]
  simp [historyReport, historyWritten, historyWrite, historyWriteSerial,
    List.filterMap_append, eventWrite, eventReport]

theorem overlayReplay_writeReport_written
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage)
    (bit truth : Bool) (serial : ℕ) (decision : Bool)
    (hd : (simulatorDrawRecord (draw seed stage (overlayReplay draw mark ghost seed history).shadow)).decision =
      some decision) :
    let record := simulatorDrawRecord (draw seed stage (overlayReplay draw mark ghost seed history).shadow)
    historyWrite (overlayReplay draw mark ghost seed
      (history ++ [.wrote stage bit serial, .report stage truth serial])).shadow stage =
      some (decision,
        (historyActions (overlayReplay draw mark ghost seed history).shadow).length + record.observations.length) := by
  dsimp only
  rw [show history ++ [.wrote stage bit serial, .report stage truth serial] =
    (history ++ [.wrote stage bit serial]) ++ [.report stage truth serial] by simp]
  rw [overlayReplay_append_event, overlayReplay_append_event]
  simp only [overlayStep, simulatorStep, simulatorAppend]
  simp [historyWrite, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, eventWrite, hd]

/-- Exact OR law at the REAL early report, for every seed/path and arbitrary
old non-MAP writing decision. This does not claim any distributional gate law. -/
theorem overlayReplay_writeReport_error
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage)
    (bit truth : Bool) (serial : ℕ) (decision : Bool)
    (hd : (simulatorDrawRecord (draw seed stage (overlayReplay draw mark ghost seed history).shadow)).decision =
      some decision) :
    let record := simulatorDrawRecord (draw seed stage (overlayReplay draw mark ghost seed history).shadow)
    reportedWriteError (overlayReplay draw mark ghost seed
      (history ++ [.wrote stage bit serial, .report stage truth serial])).shadow stage =
      some ((bit != truth) || mark seed stage record) := by
  dsimp only
  simp [reportedWriteError, overlayReplay_writeReport_report draw mark ghost seed history stage bit truth serial decision hd,
    overlayReplay_writeReport_written draw mark ghost seed history stage bit truth serial decision hd,
    overlayReportTruth_error]

end PDROC
