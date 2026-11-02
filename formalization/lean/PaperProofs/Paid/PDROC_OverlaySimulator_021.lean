module

public import PaperProofs.Paid.PDROC_OverlaySimulator_004
public import PaperProofs.Paid.PDROC_SimulatorProjection_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- The projections needed to transport stage ports. Correction lists may
strictly grow in the virtual history, so equality of those lists is absent. -/
def OverlayHistoryProjection (actual virtual : List (VisibleEvent I)) : Prop :=
  historyCursor actual = historyCursor virtual ∧
    (∀ stage, historyWritten actual stage = none ↔ historyWritten virtual stage = none) ∧
    historyHalted actual = historyHalted virtual

theorem overlayHistoryProjection_of_same {actual virtual : List (VisibleEvent I)}
    (h : SameHistoryProjection actual virtual) : OverlayHistoryProjection actual virtual :=
  ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩

theorem overlayHistoryProjection_append {actual virtual moreActual moreVirtual : List (VisibleEvent I)}
    (h : OverlayHistoryProjection actual virtual) (hm : OverlayHistoryProjection moreActual moreVirtual) :
    OverlayHistoryProjection (actual ++ moreActual) (virtual ++ moreVirtual) := by
  rcases h with ⟨hc, hw, hh⟩
  rcases hm with ⟨hc', hw', hh'⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [historyCursor_append, historyCursor_append, hc, hc']
  · intro stage
    rw [historyWritten_none_append, historyWritten_none_append, hw stage, hw' stage]
  · rw [historyHalted_append, historyHalted_append, hh, hh']

theorem overlayHistoryProjection_ghostEvents (calls : List (OverlayGhostCall I)) :
    OverlayHistoryProjection [] (overlayGhostEvents calls) := by
  induction calls with
  | nil => exact ⟨rfl, fun _ => Iff.rfl, rfl⟩
  | cons call rest ih =>
    have hc : OverlayHistoryProjection [] (overlayGhostEvents [call]) := by
      rcases call with ⟨reserve, handle, tool⟩
      cases reserve <;> simp [OverlayHistoryProjection, overlayGhostEvents, historyCursor,
        historyWritten, historyWrite, historyHalted, historyActions, List.filterMap_cons,
        List.filterMap_nil, eventAdvance, eventWrite, eventAction]
    simpa only [overlayGhostEvents, List.map_cons, List.map_nil, List.singleton_append, List.nil_append]
      using overlayHistoryProjection_append hc ih

theorem overlayHistoryProjection_reviewPacket (stage : I.Stage) (record : AuxiliaryRecord) :
    OverlayHistoryProjection [] (simulatorReviewPacket stage record) :=
  overlayHistoryProjection_of_same (sameHistoryProjection_reviewPacket stage record)

theorem overlayStep_historyProjection {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I)
    (h : OverlayHistoryProjection cache.seen cache.shadow) :
    OverlayHistoryProjection (overlayStep draw mark ghost seed cache event).seen
      (overlayStep draw mark ghost seed cache event).shadow := by
  have hsingle (e e' : VisibleEvent I) (he : OverlayHistoryProjection [e] [e']) :=
    overlayHistoryProjection_append h he
  cases event with
  | observation stage symbol =>
    exact overlayHistoryProjection_append h (by
      simp [OverlayHistoryProjection, historyCursor, historyWritten, historyWrite,
        historyHalted, historyActions, eventAdvance, eventWrite, eventAction])
  | wrote stage bit serial =>
    dsimp only [overlayStep, simulatorStep, simulatorAppend]
    apply overlayHistoryProjection_append h
    apply overlayHistoryProjection_append (overlayHistoryProjection_reviewPacket stage _)
    simp [OverlayHistoryProjection, historyCursor, historyWritten, historyWrite,
      historyHalted, historyActions, List.filterMap_cons, List.filterMap_nil,
      eventAdvance, eventWrite, eventAction]
    intro other
    by_cases hs : stage = other <;> simp [hs]
  | report | committed | executed =>
    apply hsingle
    all_goals simp [OverlayHistoryProjection, historyCursor, historyWritten, historyWrite,
      historyHalted, historyActions, List.filterMap_cons, List.filterMap_nil,
      eventAdvance, eventWrite, eventAction]
  | advanced stage =>
    apply overlayHistoryProjection_append h
    exact overlayHistoryProjection_append (overlayHistoryProjection_ghostEvents _)
      ⟨rfl, fun _ => Iff.rfl, rfl⟩
  | stopped | abandoned =>
    dsimp only [overlayStep]
    split_ifs
    all_goals apply overlayHistoryProjection_append h
    all_goals first
    | exact overlayHistoryProjection_append
        (overlayHistoryProjection_append (overlayHistoryProjection_reviewPacket _ _) (overlayHistoryProjection_ghostEvents _))
        ⟨rfl, fun _ => Iff.rfl, rfl⟩
    | exact overlayHistoryProjection_append (overlayHistoryProjection_ghostEvents _)
        ⟨rfl, fun _ => Iff.rfl, rfl⟩

theorem overlayReplay_historyProjection {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) :
    OverlayHistoryProjection history (overlayReplay draw mark ghost seed history).shadow := by
  have hfold (events : List (VisibleEvent I)) (cache : SimulatorCache I)
      (h : OverlayHistoryProjection cache.seen cache.shadow) :
      OverlayHistoryProjection (events.foldl (overlayStep draw mark ghost seed) cache).seen
        (events.foldl (overlayStep draw mark ghost seed) cache).shadow := by
    induction events generalizing cache with
    | nil => exact h
    | cons event events ih => exact ih _ (overlayStep_historyProjection draw mark ghost seed cache event h)
  have h := hfold history (simulatorInitialCache I) ⟨rfl, fun _ => Iff.rfl, rfl⟩
  change OverlayHistoryProjection (overlayReplay draw mark ghost seed history).seen
    (overlayReplay draw mark ghost seed history).shadow at h
  rw [overlayReplay_seen] at h
  exact h

end PDROC
