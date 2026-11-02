module

public import PaperProofs.Paid.PDROC_OverlaySimulator_035
public import PaperProofs.Paid.PDROC_SimulatorLaw_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem overlay_validHandle_serial (history : List (VisibleEvent I)) (handle : MismatchHandle I)
    (hv : historyValidHandle history handle) : handle.writeSerial = historyWriteSerial history handle.stage := by
  unfold historyValidHandle at hv
  cases hr : historyReport history handle.stage with
  | none => rw [hr] at hv; exact hv.elim
  | some pair => rw [hr] at hv; exact hv.2.2.symm

/-- Exact full shadow response for a physical postwrite action when no ghost
is inserted. Source permissions give the correct virtual handle serial. -/
theorem overlayReplay_postwrite_response {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage)
    (hc : historyCursor history = stage.val) (hw : historyWritten history stage ≠ none)
    (hg : ghost seed (overlayReplay draw mark ghost seed history) = []) (action : Action I)
    (hallow : historyAllowsAction (overlayReplay draw mark ghost seed history).shadow action) :
    (overlayReplay draw mark ghost seed
      (history ++ postwriteResponse (reserialAction history (fun _ bit => bit) action))).shadow =
      (overlayReplay draw mark ghost seed history).shadow ++ postwriteResponse action := by
  let virtual := (overlayReplay draw mark ghost seed history).shadow
  have hproj := overlayReplay_historyProjection draw mark ghost seed history
  have hstage (current : I.Stage) (hcur : historyCursor virtual = current.val) : current = stage :=
    Fin.ext (hcur.symm.trans (hproj.1.symm.trans hc))
  cases action with
  | review current =>
    have he := hstage current hallow.1
    subst current
    exact (hw ((hproj.2.1 stage).mpr hallow.2)).elim
  | write current bit =>
    have he := hstage current hallow.1
    subst current
    exact (hw ((hproj.2.1 stage).mpr hallow.2)).elim
  | allocate handle tool =>
    have hs := overlay_validHandle_serial virtual handle hallow.2.1
    simp only [reserialAction, postwriteResponse, overlayReplay_append_event, overlayStep, simulatorStep, simulatorAppend]
    rw [reserialHandle_roundtrip (overlayReplay draw mark ghost seed history).shadow history handle hs]
  | execute handle tool =>
    have hs := overlay_validHandle_serial virtual handle hallow.2.1
    simp only [reserialAction, postwriteResponse, overlayReplay_append_event, overlayStep, simulatorStep, simulatorAppend]
    rw [reserialHandle_roundtrip (overlayReplay draw mark ghost seed history).shadow history handle hs]
  | advance current =>
    simp only [reserialAction, postwriteResponse, overlayReplay_append_event, overlayStep, simulatorAppend, hg, overlayGhostEvents, List.map_nil, List.nil_append]
  | stop =>
    have hlt : historyCursor (overlayReplay draw mark ghost seed history).seen < I.stageCount := by
      rw [overlayReplay_seen, hc]
      exact stage.isLt
    have he : (⟨historyCursor (overlayReplay draw mark ghost seed history).seen, hlt⟩ : I.Stage) = stage :=
      Fin.ext (by simpa only [overlayReplay_seen] using hc)
    have hwn : historyWritten (overlayReplay draw mark ghost seed history).seen stage ≠ none := by
      simpa only [overlayReplay_seen] using hw
    simp only [reserialAction, postwriteResponse, overlayReplay_append_event, overlayStep,
      hlt, ↓reduceDIte, he, hwn, ite_false, simulatorAppend, hg, overlayGhostEvents, List.map_nil, List.nil_append]
  | abandon =>
    have hlt : historyCursor (overlayReplay draw mark ghost seed history).seen < I.stageCount := by
      rw [overlayReplay_seen, hc]
      exact stage.isLt
    have he : (⟨historyCursor (overlayReplay draw mark ghost seed history).seen, hlt⟩ : I.Stage) = stage :=
      Fin.ext (by simpa only [overlayReplay_seen] using hc)
    have hwn : historyWritten (overlayReplay draw mark ghost seed history).seen stage ≠ none := by
      simpa only [overlayReplay_seen] using hw
    simp only [reserialAction, postwriteResponse, overlayReplay_append_event, overlayStep,
      hlt, ↓reduceDIte, he, hwn, ite_false, simulatorAppend, hg, overlayGhostEvents, List.map_nil, List.nil_append]

end PDROC
