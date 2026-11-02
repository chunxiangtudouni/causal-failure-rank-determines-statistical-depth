module

public import PaperProofs.Paid.PDROC_TerminalCapture_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native

namespace PDROC

variable {I : Instance} {Source : Type*} [MeasurableSpace Source]

/-- Natural cursor version also includes terminal cursor N and N=0. -/
def cursorCompletedNatHistory (cursor : ℕ) : EntryHistory I → EntryHistory I
  | none => none
  | some history => if historyCursor history = cursor then some history else none

def cursorCompletedNatProjection (cursor : ℕ) (pair : Source × EntryHistory I) : Source × EntryHistory I :=
  (pair.1, cursorCompletedNatHistory cursor pair.2)

theorem measurable_cursorCompletedNatProjection (cursor : ℕ) :
    Measurable (cursorCompletedNatProjection (I := I) (Source := Source) cursor) :=
  measurable_fst.prodMk ((measurable_of_countable (cursorCompletedNatHistory cursor)).comp measurable_snd)

theorem map_cursorCompletedNatProjection_restrict (ρ : Measure (Source × EntryHistory I)) (cursor : ℕ) :
    (ρ.map (cursorCompletedNatProjection cursor)).restrict (completedCursorCell I Source cursor) =
      ρ.restrict (completedCursorCell I Source cursor) := by
  ext A hA
  rw [Measure.restrict_apply hA, Measure.map_apply (measurable_cursorCompletedNatProjection cursor)
    (hA.inter (measurableSet_completedCursorCell cursor)), Measure.restrict_apply hA]
  congr 1
  ext pair
  rcases pair with ⟨seed, history⟩
  cases history with
  | none => simp [cursorCompletedNatProjection, cursorCompletedNatHistory, completedCursorCell]
  | some history =>
    by_cases hc : historyCursor history = cursor <;>
      simp [cursorCompletedNatProjection, cursorCompletedNatHistory, completedCursorCell, hc]

theorem completedCursor_restrict_eq_of_natProjectionLaw (ρ σ : Measure (Source × EntryHistory I))
    (cursor : ℕ)
    (hlaw : ρ.map (cursorCompletedNatProjection cursor) = σ.map (cursorCompletedNatProjection cursor)) :
    ρ.restrict (completedCursorCell I Source cursor) = σ.restrict (completedCursorCell I Source cursor) := by
  rw [← map_cursorCompletedNatProjection_restrict ρ cursor,
    ← map_cursorCompletedNatProjection_restrict σ cursor, hlaw]

omit [MeasurableSpace Source] in
theorem cursorCompletedNatProjection_stage (stage : I.Stage) :
    cursorCompletedNatProjection (Source := Source) stage.val = cursorCompletedProjection stage := rfl

end PDROC
