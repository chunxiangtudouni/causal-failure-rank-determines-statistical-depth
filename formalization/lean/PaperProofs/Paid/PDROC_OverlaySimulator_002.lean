module

public import PaperProofs.Paid.PDROC_OverlaySimulator_001
public import PaperProofs.Paid.PDROC_Simulator_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {SimSeed : Type u}

/-- Virtual-only reservations/executions. This type cannot carry a truth
report, ordinary write, review, advance or termination. -/
abbrev OverlayGhostCall (I : Instance) := Bool × (MismatchHandle I × I.Tool)

def overlayGhostEvents (calls : List (OverlayGhostCall I)) : List (VisibleEvent I) :=
  calls.map fun call => if call.1 then .committed call.2.1 call.2.2 else .executed call.2.1 call.2.2

theorem overlayGhostEvents_no_report (calls : List (OverlayGhostCall I)) (stage : I.Stage) :
    (overlayGhostEvents calls).filterMap (eventReport stage) = [] := by
  induction calls with
  | nil => rfl
  | cons call rest ih =>
    cases call with
    | mk reserve pair =>
      cases reserve <;> change (overlayGhostEvents rest).filterMap (eventReport stage) = []
      all_goals exact ih

/-- A causal overlay transducer. Fresh marks are selected by the auxiliary
record. Ghost calls are inserted only at physical advance/termination;
every actual physical call is always retained with its virtual serial.
No virtual report can be produced before a real report event arrives. -/
def overlayStep
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) : SimulatorCache I :=
  match event with
  | .report stage truth _ =>
      let record := (cache.chosen stage).getD simulatorEmptyRecord
      let oldBit := record.decision.getD ((historyWritten cache.shadow stage).getD false)
      let realBit := (historyWritten cache.seen stage).getD false
      simulatorAppend cache event [.report stage
        (overlayReportTruth realBit oldBit truth (mark seed stage record))
        (historyWriteSerial cache.shadow stage)]
  | .advanced stage =>
      simulatorAppend cache event (overlayGhostEvents (ghost seed cache) ++ [.advanced stage])
  | .stopped | .abandoned =>
      let calls := overlayGhostEvents (ghost seed cache)
      if hstage : historyCursor cache.seen < I.stageCount then
        let stage : I.Stage := ⟨historyCursor cache.seen, hstage⟩
        if historyWritten cache.seen stage = none then
          let record := simulatorDrawRecord (draw seed stage cache.shadow)
          simulatorAppend cache event (simulatorReviewPacket stage record ++ calls ++ [event])
        else simulatorAppend cache event (calls ++ [event])
      else simulatorAppend cache event (calls ++ [event])
  | event => simulatorStep draw seed cache event

def overlayReplay
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) : SimulatorCache I :=
  history.foldl (overlayStep draw mark ghost seed) (simulatorInitialCache I)

theorem overlayStep_seen
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) :
    (overlayStep draw mark ghost seed cache event).seen = cache.seen ++ [event] := by
  cases event <;> simp only [overlayStep, simulatorStep, simulatorAppend]
  all_goals split_ifs <;> rfl

theorem overlayStep_shadow_prefix
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) :
    cache.shadow.IsPrefix (overlayStep draw mark ghost seed cache event).shadow := by
  cases event <;> simp only [overlayStep, simulatorStep, simulatorAppend]
  all_goals (try split_ifs) <;> exact List.prefix_append _ _

theorem overlayReplay_seen
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) :
    (overlayReplay draw mark ghost seed history).seen = history := by
  have hfold (history : List (VisibleEvent I)) (cache : SimulatorCache I) :
      (history.foldl (overlayStep draw mark ghost seed) cache).seen = cache.seen ++ history := by
    induction history generalizing cache with
    | nil => simp
    | cons event rest ih =>
      simp only [List.foldl_cons, ih, overlayStep_seen, List.append_assoc, List.singleton_append]
  exact hfold history (simulatorInitialCache I)

theorem overlayFold_shadow_prefix
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (cache : SimulatorCache I) :
    cache.shadow.IsPrefix (history.foldl (overlayStep draw mark ghost seed) cache).shadow := by
  induction history generalizing cache with
  | nil => exact List.prefix_refl _
  | cons event rest ih =>
    exact (overlayStep_shadow_prefix draw mark ghost seed cache event).trans
      (ih (overlayStep draw mark ghost seed cache event))

theorem overlayReplay_shadow_causal
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (before after : List (VisibleEvent I)) (hp : before.IsPrefix after) :
    (overlayReplay draw mark ghost seed before).shadow.IsPrefix
      (overlayReplay draw mark ghost seed after).shadow := by
  obtain ⟨rest, rfl⟩ := hp
  simp only [overlayReplay, List.foldl_append]
  exact overlayFold_shadow_prefix draw mark ghost seed rest _

end PDROC
