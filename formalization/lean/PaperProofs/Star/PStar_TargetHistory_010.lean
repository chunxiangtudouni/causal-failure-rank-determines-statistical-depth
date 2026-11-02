module

public import PaperProofs.Star.PStar_CurrentChoice_001
public import PaperProofs.Common.NativeHeadTest

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarTargetHistory010

open Common Common.Native Parameters

/-- The original adaptive selector uses only genuine ordinary writes and
versioned reports. Reviews, commitments and executions do not change it. -/
theorem chosenTargetReal_congr (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (left right : List (VisibleEvent (starInstance P.tools order)))
    (writes : ∀ stage, historyWritten left stage = historyWritten right stage)
    (reports : ∀ stage, historyReport left stage = historyReport right stage)
    (stage : (starInstance P.tools order).Stage) :
    P.chosenTargetReal order kind r left stage = P.chosenTargetReal order kind r right stage := by
  have errors : ∀ i, reportedError left i = reportedError right i := by
    intro i
    simp only [reportedError, writes i, reports i]
  have previous : previousAllErrors left stage = previousAllErrors right stage := by
    simp only [previousAllErrors, errors]
  cases kind <;> cases order <;> simp only [Parameters.chosenTargetReal, errors, previous]

theorem chosenTargetReal_append_observation (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (r : ℝ) (history : List (VisibleEvent (starInstance P.tools order)))
    (reviewStage stage : (starInstance P.tools order).Stage) (symbol : ℕ) :
    P.chosenTargetReal order kind r (history ++ [.observation reviewStage symbol]) stage =
      P.chosenTargetReal order kind r history stage := by
  apply chosenTargetReal_congr
  · intro i
    simp only [historyWritten, historyWrite, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, eventWrite, List.append_nil]
  · intro i
    simp only [historyReport, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, eventReport, List.append_nil]

/-- Fixed target during any original local review block, including adaptive
count selection and the UF second test. No supplied stability oracle. -/
theorem chosenTargetReal_append_headReviewHistory (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (r : ℝ) (history : List (VisibleEvent (starInstance P.tools order)))
    (reviewStage stage : (starInstance P.tools order).Stage)
    (tape : ((P.input order).experiment reviewStage).Tape) (n : ℕ) :
    P.chosenTargetReal order kind r
      (history ++ headReviewHistory (P.input order) reviewStage tape n) stage =
        P.chosenTargetReal order kind r history stage := by
  induction n with
  | zero => simp only [headReviewHistory, List.ofFn_zero, List.append_nil]
  | succ n ih =>
    rw [headReviewHistory_succ, ← List.append_assoc,
      chosenTargetReal_append_observation, ih]

theorem previousAllErrors_iff {I : Instance} (history : List (VisibleEvent I)) (stage : I.Stage) :
    previousAllErrors history stage = true ↔ ∀ earlier : I.Stage,
      earlier.val < stage.val → reportedError history earlier = true := by
  unfold previousAllErrors
  rw [List.all_eq_true]
  constructor
  · intro all earlier before
    have h := all _ (List.mem_ofFn.mpr ⟨earlier, rfl⟩)
    simpa only [id_eq, before, decide_true, Bool.not_true, Bool.false_or] using h
  · intro all bit member
    obtain ⟨earlier, rfl⟩ := List.mem_ofFn.mp member
    by_cases before : earlier.val < stage.val
    · simp only [id_eq, before, decide_true, Bool.not_true, Bool.false_or, all earlier before]
    · simp only [id_eq, before, decide_false, Bool.not_false, Bool.true_or]

end PaperProofs.Star.PStarTargetHistory010
