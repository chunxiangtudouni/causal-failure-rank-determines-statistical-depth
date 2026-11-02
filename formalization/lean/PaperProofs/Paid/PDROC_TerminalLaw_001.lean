module

public import PaperProofs.Paid.PDROC_Postwrite_001
public import Mathlib.MeasureTheory.Measure.Restrict

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance} {Source : Type*} [MeasurableSpace Source]

def completedCursorCell (I : Instance) (Source : Type*) (cursor : ℕ) : Set (Source × EntryHistory I) :=
  {pair | pair.2.map historyCursor = some cursor}

theorem measurableSet_completedCursorCell (cursor : ℕ) :
    MeasurableSet (completedCursorCell I Source cursor) :=
  measurable_snd (MeasurableSpace.measurableSet_top
    (s := {history : EntryHistory I | history.map historyCursor = some cursor}))

/-- Finite terminal-cursor restriction laws determine the FULL old-seed ×
completed-history law. Earlier terminal histories are retained as atoms;
there is no measurable-range or conditional-probability assumption. -/
theorem completedJointLaw_eq_of_cursor_restrictions
    (ρ σ : Measure (Source × EntryHistory I))
    (hρ : ∀ᵐ pair ∂ρ, ∃ history, pair.2 = some history ∧ historyCursor history ≤ I.stageCount)
    (hσ : ∀ᵐ pair ∂σ, ∃ history, pair.2 = some history ∧ historyCursor history ≤ I.stageCount)
    (hcursor : ∀ cursor : Fin (I.stageCount + 1),
      ρ.restrict (completedCursorCell I Source cursor.val) = σ.restrict (completedCursorCell I Source cursor.val)) :
    ρ = σ := by
  let cells : Fin (I.stageCount + 1) → Set (Source × EntryHistory I) :=
    fun cursor => completedCursorCell I Source cursor.val
  have hcoverρ : ∀ᵐ pair ∂ρ, pair ∈ ⋃ cursor, cells cursor := by
    filter_upwards [hρ] with pair hp
    obtain ⟨history, hh, hb⟩ := hp
    apply Set.mem_iUnion.mpr
    refine ⟨⟨historyCursor history, by omega⟩, ?_⟩
    simp only [cells, completedCursorCell, Set.mem_ofPred_eq, hh, Option.map_some]
  have hcoverσ : ∀ᵐ pair ∂σ, pair ∈ ⋃ cursor, cells cursor := by
    filter_upwards [hσ] with pair hp
    obtain ⟨history, hh, hb⟩ := hp
    apply Set.mem_iUnion.mpr
    refine ⟨⟨historyCursor history, by omega⟩, ?_⟩
    simp only [cells, completedCursorCell, Set.mem_ofPred_eq, hh, Option.map_some]
  calc
    ρ = ρ.restrict (⋃ cursor, cells cursor) := (Measure.restrict_eq_self_of_ae_mem hcoverρ).symm
    _ = σ.restrict (⋃ cursor, cells cursor) := Measure.restrict_iUnion_congr.mpr hcursor
    _ = σ := Measure.restrict_eq_self_of_ae_mem hcoverσ

theorem completedHistory_cursor_bound {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hl : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (history : List (VisibleEvent I))
    (hh : completedHistory input C mode accounting rule sample = some history) :
    historyCursor history ≤ I.stageCount := by
  obtain ⟨n, _, _, hhistory⟩ := (completedHistory_some_iff input C mode accounting rule sample history).mp hh
  obtain ⟨k, _, hp⟩ := run_has_prefix input C mode accounting rule hl sample n
  rw [← hhistory, prefix_historyCursor input C mode accounting rule sample.1 _ _ hp]
  exact (run_cursorInvariant input C mode accounting rule hl sample n).bound

end PDROC
