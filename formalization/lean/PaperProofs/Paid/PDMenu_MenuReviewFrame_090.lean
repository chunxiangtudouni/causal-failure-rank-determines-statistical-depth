module

public import PaperProofs.Paid.PDMenu_MenuSnapshotPackets_085
public import PaperProofs.Common.NativeBellmanHistoryLift

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance}

theorem menuReviewPacket_filterMap_none {A : Type*} (input : StatisticalInput I) (stage : I.Stage)
    (tape : (input.experiment stage).Tape) (n : ℕ) (f : VisibleEvent I → Option A)
    (hnone : ∀ symbol, f (.observation stage symbol) = none) :
    (headReviewHistory input stage tape n).filterMap f = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro event he
  change event ∈ List.ofFn (fun i : Fin n => VisibleEvent.observation stage (tape i.val).val) at he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact hnone (tape i.val).val

theorem menuReviewPacket_halted (input : StatisticalInput I) (stage : I.Stage)
    (tape : (input.experiment stage).Tape) (n : ℕ) :
    historyHalted (headReviewHistory input stage tape n) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [headReviewHistory_succ, historyHalted, historyActions, List.filterMap_append,
      List.filterMap_cons, eventAction, List.filterMap_nil, List.any_append, List.any_cons,
      List.any_nil, Bool.or_false] using ih

theorem menuReviewFrame_cursor (input : StatisticalInput I) (stage : I.Stage)
    (tape : (input.experiment stage).Tape) (n : ℕ) (before : List (VisibleEvent I)) :
    historyCursor (before ++ headReviewHistory input stage tape n) = historyCursor before := by
  calc
    _ = historyCursor before + historyCursor (headReviewHistory input stage tape n) := by
      simp only [historyCursor, List.filterMap_append, List.length_append]
    _ = _ := by rw [historyCursor_headReviewHistory, Nat.add_zero]

theorem menuReviewFrame_halted (input : StatisticalInput I) (stage : I.Stage)
    (tape : (input.experiment stage).Tape) (n : ℕ) (before : List (VisibleEvent I)) :
    historyHalted (before ++ headReviewHistory input stage tape n) = historyHalted before := by
  calc
    _ = (historyHalted before || historyHalted (headReviewHistory input stage tape n)) := by
      simp only [historyHalted, historyActions, List.filterMap_append, List.any_append]
    _ = _ := by rw [menuReviewPacket_halted, Bool.or_false]

theorem menuReviewFrame_write (input : StatisticalInput I) (stage : I.Stage)
    (tape : (input.experiment stage).Tape) (n : ℕ) (before : List (VisibleEvent I)) :
    historyWrite (before ++ headReviewHistory input stage tape n) stage = historyWrite before stage := by
  unfold historyWrite
  rw [List.filterMap_append, menuReviewPacket_filterMap_none input stage tape n (eventWrite stage) (by intro; rfl),
    List.append_nil]

theorem menuReviewFrame_observations (input : StatisticalInput I) (stage : I.Stage)
    (tape : (input.experiment stage).Tape) (n : ℕ) (before : List (VisibleEvent I)) :
    historyObservations (before ++ headReviewHistory input stage tape n) stage =
      historyObservations before stage ++ List.ofFn (fun i : Fin n => (tape i.val).val) := by
  calc
    _ = historyObservations before stage ++ historyObservations (headReviewHistory input stage tape n) stage := by
      simp only [historyObservations, List.filterMap_append]
    _ = _ := congrArg (fun observations => historyObservations before stage ++ observations)
      (historyObservations_headReviewHistory input stage tape n)

theorem menuReviewFrame_entryTools (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : (freshInstance N K).Stage) (tape : ((P.freshInput N K fee hfee).experiment stage).Tape)
    (n : ℕ) (before : List (VisibleEvent (freshInstance N K))) :
    P.menuEntryTools N K (before ++ headReviewHistory (P.freshInput N K fee hfee) stage tape n) stage =
      P.menuEntryTools N K before stage :=
  menuEntryTools_append_no_execution P N K before _ stage
    (headReviewHistory_empty_corrections (P.freshInput N K fee hfee) stage tape n).2

end PDMenu
