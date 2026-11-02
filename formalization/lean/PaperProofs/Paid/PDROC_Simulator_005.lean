module

public import PaperProofs.Paid.PDROC_Simulator_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {SimSeed : Type u}

theorem simulatorFold_observations
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (stage : I.Stage) (letters : List (Fin 2)) (cache : SimulatorCache I) :
    ((letters.map (fun symbol => VisibleEvent.observation stage symbol.val)).foldl
      (simulatorStep draw seed) cache) =
      {cache with seen := cache.seen ++ letters.map (fun symbol => .observation stage symbol.val)} := by
  induction letters generalizing cache with
  | nil => simp
  | cons letter rest ih =>
    simp only [List.map_cons, List.foldl_cons, simulatorStep, simulatorAppend, List.append_nil,
      ih, List.append_assoc, List.singleton_append]

theorem simulatorReplay_append_observations
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (entry : List (VisibleEvent I)) (stage : I.Stage) (letters : List (Fin 2)) :
    simulatorReplay draw seed (entry ++ letters.map (fun symbol => .observation stage symbol.val)) =
      {simulatorReplay draw seed entry with
        seen := entry ++ letters.map (fun symbol => .observation stage symbol.val)} := by
  simp only [simulatorReplay, List.foldl_append, simulatorFold_observations]
  rw [← simulatorReplay, simulatorReplay_seen]

theorem historyCursor_append_observations (entry : List (VisibleEvent I))
    (stage : I.Stage) (letters : List (Fin 2)) :
    historyCursor (entry ++ letters.map (fun symbol => .observation stage symbol.val)) = historyCursor entry := by
  simp [historyCursor, List.filterMap_append, List.filterMap_map, eventAdvance]

theorem historyWritten_append_observations (entry : List (VisibleEvent I))
    (stage queried : I.Stage) (letters : List (Fin 2)) :
    historyWritten (entry ++ letters.map (fun symbol => .observation stage symbol.val)) queried =
      historyWritten entry queried := by
  simp [historyWritten, historyWrite, List.filterMap_append, List.filterMap_map, eventWrite, Function.comp_def]

theorem historyHalted_append_observations (entry : List (VisibleEvent I))
    (stage : I.Stage) (letters : List (Fin 2)) :
    historyHalted (entry ++ letters.map (fun symbol => .observation stage symbol.val)) = historyHalted entry := by
  simp [historyHalted, historyActions, List.filterMap_append, List.filterMap_map, eventAction]

theorem historyObservations_append_observations_self (entry : List (VisibleEvent I))
    (stage : I.Stage) (letters : List (Fin 2)) :
    historyObservations (entry ++ letters.map (fun symbol => .observation stage symbol.val)) stage =
      historyObservations entry stage ++ letters.map Fin.val := by
  simp [historyObservations, List.filterMap_append, List.filterMap_map, eventObservation, Function.comp_def]

variable {Seed : Type u}

theorem simulatorShadow_append_observations (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed)
    (entry : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage) (letters : List (Fin 2)) :
    simulatorShadow P fee hfee source seed (entry ++ letters.map (fun symbol => .observation stage symbol.val)) =
      simulatorShadow P fee hfee source seed entry := by
  unfold simulatorShadow
  rw [simulatorReplay_append_observations]

end PDROC
