module

public import PaperProofs.Paid.PDROC_Simulator_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

def SameHistoryProjection (actual virtual : List (VisibleEvent I)) : Prop :=
  historyCursor actual = historyCursor virtual ∧
    reservedPairs actual = reservedPairs virtual ∧ executedPairs actual = executedPairs virtual ∧
    (∀ stage, historyWritten actual stage = none ↔ historyWritten virtual stage = none) ∧
    historyHalted actual = historyHalted virtual

theorem historyWritten_none_append (before after : List (VisibleEvent I)) (stage : I.Stage) :
    historyWritten (before ++ after) stage = none ↔
      historyWritten before stage = none ∧ historyWritten after stage = none := by
  simp [historyWritten, historyWrite, List.filterMap_append, and_comm]

theorem historyCursor_append (before after : List (VisibleEvent I)) :
    historyCursor (before ++ after) = historyCursor before + historyCursor after := by
  simp [historyCursor, List.filterMap_append]

theorem historyHalted_append (before after : List (VisibleEvent I)) :
    historyHalted (before ++ after) = (historyHalted before || historyHalted after) := by
  simp [historyHalted, historyActions, List.filterMap_append]

theorem sameHistoryProjection_append {actual virtual moreActual moreVirtual : List (VisibleEvent I)}
    (h : SameHistoryProjection actual virtual) (hmore : SameHistoryProjection moreActual moreVirtual) :
    SameHistoryProjection (actual ++ moreActual) (virtual ++ moreVirtual) := by
  rcases h with ⟨hcu, hr, he, hp, hh⟩
  rcases hmore with ⟨hcu', hr', he', hp', hh'⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [historyCursor_append, historyCursor_append, hcu, hcu']
  · rw [reservedPairs_append, reservedPairs_append, hr, hr']
  · rw [executedPairs_append, executedPairs_append, he, he']
  · intro stage
    rw [historyWritten_none_append, historyWritten_none_append, hp stage, hp' stage]
  · rw [historyHalted_append, historyHalted_append, hh, hh']

theorem sameHistoryProjection_reviewPacket (stage : I.Stage) (record : AuxiliaryRecord) :
    SameHistoryProjection [] (simulatorReviewPacket stage record) := by
  simp [SameHistoryProjection, simulatorReviewPacket, historyCursor, reservedPairs, executedPairs,
    historyCommitments, historyExecutions, historyWritten, historyWrite, historyHalted, historyActions,
    List.filterMap_map, Function.comp_def, eventAdvance, eventCommitment, eventExecution, eventWrite, eventAction]

theorem simulatorStep_sameProjection {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I)
    (h : SameHistoryProjection cache.seen cache.shadow) :
    SameHistoryProjection (simulatorStep draw seed cache event).seen
      (simulatorStep draw seed cache event).shadow := by
  have hsingle (e e' : VisibleEvent I)
      (he : SameHistoryProjection [e] [e']) := sameHistoryProjection_append h he
  cases event with
  | observation stage symbol =>
    exact sameHistoryProjection_append h (by
      simp [SameHistoryProjection, historyCursor, reservedPairs, executedPairs, historyCommitments,
        historyExecutions, historyWritten, historyWrite, historyHalted, historyActions,
        eventAdvance, eventCommitment, eventExecution, eventWrite, eventAction])
  | wrote stage bit serial =>
    dsimp only [simulatorStep, simulatorAppend]
    apply sameHistoryProjection_append h
    have hp := sameHistoryProjection_append (sameHistoryProjection_reviewPacket stage
      (simulatorDrawRecord (draw seed stage cache.shadow)))
      (show SameHistoryProjection [.wrote stage bit serial]
        [.wrote stage ((simulatorDrawRecord (draw seed stage cache.shadow)).decision.getD bit)
          ((historyActions cache.shadow).length + (simulatorDrawRecord (draw seed stage cache.shadow)).observations.length)] by
        simp [SameHistoryProjection, historyCursor, reservedPairs, executedPairs, historyCommitments,
          historyExecutions, historyWritten, historyWrite, historyHalted, historyActions,
          List.filterMap_cons, List.filterMap_nil, eventAdvance, eventCommitment, eventExecution, eventWrite, eventAction]
        intro other
        by_cases hs : stage = other <;> simp [hs])
    exact hp
  | report stage truth serial =>
    apply hsingle
    simp [SameHistoryProjection, historyCursor, reservedPairs, executedPairs, historyCommitments,
      historyExecutions, historyWritten, historyWrite, historyHalted, historyActions,
      List.filterMap_cons, List.filterMap_nil, eventAdvance, eventCommitment, eventExecution, eventWrite, eventAction]
  | committed handle tool =>
    apply hsingle
    simp [SameHistoryProjection, historyCursor, reservedPairs, executedPairs, historyCommitments,
      historyExecutions, historyWritten, historyWrite, historyHalted, historyActions,
      List.filterMap_cons, List.filterMap_nil, eventAdvance, eventCommitment, eventExecution, eventWrite, eventAction]
  | executed handle tool =>
    apply hsingle
    simp [SameHistoryProjection, historyCursor, reservedPairs, executedPairs, historyCommitments,
      historyExecutions, historyWritten, historyWrite, historyHalted, historyActions,
      List.filterMap_cons, List.filterMap_nil, eventAdvance, eventCommitment, eventExecution, eventWrite, eventAction]
  | advanced stage => exact sameHistoryProjection_append h ⟨rfl, rfl, rfl, fun _ => Iff.rfl, rfl⟩
  | stopped | abandoned =>
    dsimp only [simulatorStep]
    split_ifs
    all_goals try exact sameHistoryProjection_append h ⟨rfl, rfl, rfl, fun _ => Iff.rfl, rfl⟩
    all_goals
      apply sameHistoryProjection_append h
      exact sameHistoryProjection_append (sameHistoryProjection_reviewPacket _ _) ⟨rfl, rfl, rfl, fun _ => Iff.rfl, rfl⟩

theorem simulatorReplay_sameProjection {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) :
    SameHistoryProjection history (simulatorReplay draw seed history).shadow := by
  have hfold (events : List (VisibleEvent I)) (cache : SimulatorCache I)
      (h : SameHistoryProjection cache.seen cache.shadow) :
      SameHistoryProjection (events.foldl (simulatorStep draw seed) cache).seen
        (events.foldl (simulatorStep draw seed) cache).shadow := by
    induction events generalizing cache with
    | nil => exact h
    | cons event events ih => exact ih _ (simulatorStep_sameProjection draw seed cache event h)
  have h := hfold history (simulatorInitialCache I) ⟨rfl, rfl, rfl, fun _ => Iff.rfl, rfl⟩
  change SameHistoryProjection (simulatorReplay draw seed history).seen
    (simulatorReplay draw seed history).shadow at h
  rw [simulatorReplay_seen] at h
  exact h

end PDROC
