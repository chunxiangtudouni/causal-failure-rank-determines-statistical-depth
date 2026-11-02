module

public import PaperProofs.Paid.PDROC_OverlaySimulator_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {SimSeed : Type u}

theorem overlayStep_pair_packet
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) :
    ∃ packet : List (VisibleEvent I),
      (overlayStep draw mark ghost seed cache event).shadow = cache.shadow ++ packet ∧
      (reservedPairs [event]).Sublist (reservedPairs packet) ∧
      (executedPairs [event]).Sublist (executedPairs packet) := by
  cases event <;> simp only [overlayStep, simulatorStep, simulatorAppend]
  all_goals (try split_ifs)
  all_goals refine ⟨_, rfl, ?_, ?_⟩
  all_goals simp [reservedPairs, executedPairs, historyCommitments, historyExecutions,
    simulatorReviewPacket, eventCommitment, eventExecution, reserialHandle,
    List.filterMap_append, List.filterMap_map, List.filterMap_cons, List.filterMap_nil,
    Function.comp_def]

theorem overlayStep_pair_sublists
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I)
    (hr : (reservedPairs cache.seen).Sublist (reservedPairs cache.shadow))
    (he : (executedPairs cache.seen).Sublist (executedPairs cache.shadow)) :
    (reservedPairs (overlayStep draw mark ghost seed cache event).seen).Sublist
        (reservedPairs (overlayStep draw mark ghost seed cache event).shadow) ∧
      (executedPairs (overlayStep draw mark ghost seed cache event).seen).Sublist
        (executedPairs (overlayStep draw mark ghost seed cache event).shadow) := by
  obtain ⟨packet, hs, hrp, hep⟩ := overlayStep_pair_packet draw mark ghost seed cache event
  rw [overlayStep_seen, hs, reservedPairs_append, reservedPairs_append,
    executedPairs_append, executedPairs_append]
  exact ⟨hr.append hrp, he.append hep⟩

/-- Every physical reservation/execution is retained, in order. This holds
on arbitrary histories, including malformed, failing and abandoned ones. -/
theorem overlayReplay_pair_sublists
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) :
    (reservedPairs history).Sublist (reservedPairs (overlayReplay draw mark ghost seed history).shadow) ∧
      (executedPairs history).Sublist (executedPairs (overlayReplay draw mark ghost seed history).shadow) := by
  have hfold (history : List (VisibleEvent I)) (cache : SimulatorCache I)
      (hr : (reservedPairs cache.seen).Sublist (reservedPairs cache.shadow))
      (he : (executedPairs cache.seen).Sublist (executedPairs cache.shadow)) :
      (reservedPairs (history.foldl (overlayStep draw mark ghost seed) cache).seen).Sublist
          (reservedPairs (history.foldl (overlayStep draw mark ghost seed) cache).shadow) ∧
        (executedPairs (history.foldl (overlayStep draw mark ghost seed) cache).seen).Sublist
          (executedPairs (history.foldl (overlayStep draw mark ghost seed) cache).shadow) := by
    induction history generalizing cache with
    | nil => exact ⟨hr, he⟩
    | cons event rest ih =>
      obtain ⟨hr', he'⟩ := overlayStep_pair_sublists draw mark ghost seed cache event hr he
      exact ih (overlayStep draw mark ghost seed cache event) hr' he'
  have h := hfold history (simulatorInitialCache I) (List.Sublist.refl _) (List.Sublist.refl _)
  change (reservedPairs (overlayReplay draw mark ghost seed history).seen).Sublist
      (reservedPairs (overlayReplay draw mark ghost seed history).shadow) ∧
    (executedPairs (overlayReplay draw mark ghost seed history).seen).Sublist
      (executedPairs (overlayReplay draw mark ghost seed history).shadow) at h
  rw [overlayReplay_seen] at h
  exact h

theorem overlayReplay_used_subset
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) :
    historyUsed history ⊆ historyUsed (overlayReplay draw mark ghost seed history).shadow :=
  historyUsed_subset_of_reservedPairs_sublist _ _
    (overlayReplay_pair_sublists draw mark ghost seed history).1

theorem overlayStep_report_count
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I) (stage : I.Stage) :
    ((overlayStep draw mark ghost seed cache event).shadow.filterMap (eventReport stage)).length =
      (cache.shadow.filterMap (eventReport stage)).length +
        ([event].filterMap (eventReport stage)).length := by
  cases event <;> simp only [overlayStep, simulatorStep, simulatorAppend]
  all_goals (try split_ifs)
  all_goals simp [List.filterMap_append, overlayGhostEvents_no_report, simulatorReviewPacket,
    List.filterMap_map, List.filterMap_cons, List.filterMap_nil, Function.comp_def, eventReport]
  all_goals split_ifs <;> rfl

theorem overlayReplay_report_count
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage) :
    ((overlayReplay draw mark ghost seed history).shadow.filterMap (eventReport stage)).length =
      (history.filterMap (eventReport stage)).length := by
  have hfold (history : List (VisibleEvent I)) (cache : SimulatorCache I) :
      ((history.foldl (overlayStep draw mark ghost seed) cache).shadow.filterMap (eventReport stage)).length =
        (cache.shadow.filterMap (eventReport stage)).length +
          (history.filterMap (eventReport stage)).length := by
    induction history generalizing cache with
    | nil => simp
    | cons event rest ih =>
      rw [List.foldl_cons, ih, overlayStep_report_count]
      simp only [List.filterMap_cons, Nat.add_assoc]
      cases eventReport stage event <;> simp [Nat.add_comm]
  simpa only [overlayReplay, simulatorInitialCache, List.filterMap_nil,
    List.length_nil, Nat.zero_add] using hfold history (simulatorInitialCache I)

/-- A virtual report exists iff the corresponding actual report exists.
This is a prefix statement, not merely an eventual/a.s. conclusion. -/
theorem overlayReplay_report_isSome
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage) :
    (historyReport (overlayReplay draw mark ghost seed history).shadow stage).isSome = true ↔
      (historyReport history stage).isSome = true := by
  simp only [historyReport, List.getLast?_isSome]
  have h := overlayReplay_report_count draw mark ghost seed history stage
  constructor
  · intro hne hz
    apply hne
    apply List.length_eq_zero_iff.mp
    rw [h, hz]
    rfl
  · intro hne hz
    apply hne
    apply List.length_eq_zero_iff.mp
    rw [← h, hz]
    rfl

end PDROC
