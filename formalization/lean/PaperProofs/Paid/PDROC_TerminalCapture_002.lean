module

public import PaperProofs.Paid.PDROC_TerminalCapture_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native

namespace PDROC

variable {I : Instance} {Source : Type*} [MeasurableSpace Source]

theorem map_cursorCompletedProjection_restrict (ρ : Measure (Source × EntryHistory I)) (stage : I.Stage) :
    (ρ.map (cursorCompletedProjection stage)).restrict (completedCursorCell I Source stage.val) =
      ρ.restrict (completedCursorCell I Source stage.val) := by
  ext A hA
  rw [Measure.restrict_apply hA, Measure.map_apply (measurable_cursorCompletedProjection stage)
    (hA.inter (measurableSet_completedCursorCell stage.val)), Measure.restrict_apply hA]
  congr 1
  ext pair
  rcases pair with ⟨seed, history⟩
  cases history with
  | none => simp [cursorCompletedProjection, cursorCompletedHistory, completedCursorCell]
  | some history =>
    by_cases hc : historyCursor history = stage.val <;>
      simp [cursorCompletedProjection, cursorCompletedHistory, completedCursorCell, hc]

theorem completedCursor_restrict_eq_of_projectionLaw (ρ σ : Measure (Source × EntryHistory I))
    (stage : I.Stage)
    (hlaw : ρ.map (cursorCompletedProjection stage) = σ.map (cursorCompletedProjection stage)) :
    ρ.restrict (completedCursorCell I Source stage.val) = σ.restrict (completedCursorCell I Source stage.val) := by
  rw [← map_cursorCompletedProjection_restrict ρ stage, ← map_cursorCompletedProjection_restrict σ stage, hlaw]

/-- A full stage-exit law and its actual native terminal captures determine
the completed joint-law restriction at this stage's terminal cursor. The
old seed coordinate and all early failed/abandoned histories remain intact. -/
theorem completedCursorLaw_eq_of_stageExitLaw
    {SampleA SampleB : Type*} [MeasurableSpace SampleA] [MeasurableSpace SampleB]
    (μ : Measure SampleA) (ν : Measure SampleB) (stage : I.Stage)
    (completeA : SampleA → Source × EntryHistory I) (hcA : Measurable completeA)
    (completeB : SampleB → Source × EntryHistory I) (hcB : Measurable completeB)
    (exitA : SampleA → (Source × EntryHistory I) × EntryHistory I) (heA : Measurable exitA)
    (exitB : SampleB → (Source × EntryHistory I) × EntryHistory I) (heB : Measurable exitB)
    (hlaw : μ.map exitA = ν.map exitB)
    (hcapA : ∀ᵐ sample ∂μ, cursorCompletedProjection stage (completeA sample) = terminalExitProjection stage (exitA sample))
    (hcapB : ∀ᵐ sample ∂ν, cursorCompletedProjection stage (completeB sample) = terminalExitProjection stage (exitB sample)) :
    (μ.map completeA).restrict (completedCursorCell I Source stage.val) =
      (ν.map completeB).restrict (completedCursorCell I Source stage.val) := by
  have hA : (μ.map completeA).map (cursorCompletedProjection stage) =
      (μ.map exitA).map (terminalExitProjection stage) := by
    rw [Measure.map_map (measurable_cursorCompletedProjection stage) hcA,
      Measure.map_map (measurable_terminalExitProjection stage) heA]
    exact Measure.map_congr hcapA
  have hB : (ν.map completeB).map (cursorCompletedProjection stage) =
      (ν.map exitB).map (terminalExitProjection stage) := by
    rw [Measure.map_map (measurable_cursorCompletedProjection stage) hcB,
      Measure.map_map (measurable_terminalExitProjection stage) heB]
    exact Measure.map_congr hcapB
  apply completedCursor_restrict_eq_of_projectionLaw _ _ stage
  exact hA.trans ((congrArg (fun ρ => ρ.map (terminalExitProjection stage)) hlaw).trans hB.symm)

end PDROC
