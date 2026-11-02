module

public import PaperProofs.Paid.PDROC_Simulator_020
public import PaperProofs.Paid.PDROC_Simulator_021

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

def simulatorSimpleMark : VisibleEvent I → Option (HistoryMark I) := simulatorMarkAt (fun _ => none)

theorem markedHistory_append_simple (before : List (VisibleEvent I)) (event : VisibleEvent I)
    (hw : ∀ stage, eventWrite stage event = none) (hr : ∀ stage, eventReport stage event = none) :
    markedHistory (before ++ [event]) = markedHistory before ++ [event].filterMap simulatorSimpleMark := by
  have hframe (stage : I.Stage) : historyWrite (before ++ [event]) stage = historyWrite before stage := by
    simp [historyWrite, List.filterMap_append, hw stage]
  rw [markedHistory_append_frame before [event] hframe]
  have hmark : simulatorMarkAt (historyWrite before) event = simulatorSimpleMark event := by
    cases event with
    | report stage truth serial => have hh := hr stage; simp only [eventReport, ↓reduceIte, reduceCtorEq] at hh
    | observation | wrote | committed | executed | advanced | stopped | abandoned => rfl
  simp only [List.filterMap_cons, List.filterMap_nil, hmark]

universe u
variable {SimSeed : Type u}

theorem simulatorStep_marks_nonwrite
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (cache : SimulatorCache I) (event : VisibleEvent I)
    (hm : markedHistory cache.seen = markedHistory cache.shadow)
    (hw : ∀ stage, eventWrite stage event = none) (hr : ∀ stage, eventReport stage event = none) :
    markedHistory (simulatorStep draw seed cache event).seen = markedHistory (simulatorStep draw seed cache event).shadow := by
  have hseen := markedHistory_append_simple cache.seen event hw hr
  rw [simulatorStep_seen, hseen, hm]
  cases event with
  | wrote stage bit serial => have hh := hw stage; simp only [eventWrite, ↓reduceIte, reduceCtorEq] at hh
  | report stage truth serial => have hh := hr stage; simp only [eventReport, ↓reduceIte, reduceCtorEq] at hh
  | observation stage symbol =>
    simp only [simulatorStep, simulatorAppend, List.append_nil]
    simp only [simulatorSimpleMark, simulatorMarkAt, List.filterMap_cons, List.filterMap_nil, List.append_nil]
  | committed handle tool =>
    rw [show (simulatorStep draw seed cache (.committed handle tool)).shadow =
      cache.shadow ++ [.committed (reserialHandle cache.shadow handle) tool] from rfl,
      markedHistory_append_simple _ _ (by intro; rfl) (by intro; rfl)]
    rfl
  | executed handle tool =>
    rw [show (simulatorStep draw seed cache (.executed handle tool)).shadow =
      cache.shadow ++ [.executed (reserialHandle cache.shadow handle) tool] from rfl,
      markedHistory_append_simple _ _ (by intro; rfl) (by intro; rfl)]
    rfl
  | advanced stage =>
    rw [show (simulatorStep draw seed cache (.advanced stage)).shadow = cache.shadow ++ [.advanced stage] from rfl,
      markedHistory_append_simple _ _ (by intro; rfl) (by intro; rfl)]
  | stopped | abandoned =>
    simp only [simulatorStep, simulatorAppend]
    split_ifs
    all_goals
      simp only [← List.append_assoc]
      rw [markedHistory_append_simple _ _ (by intro; rfl) (by intro; rfl)]
      try rw [markedHistory_append_simulatorReviews]

end PDROC
