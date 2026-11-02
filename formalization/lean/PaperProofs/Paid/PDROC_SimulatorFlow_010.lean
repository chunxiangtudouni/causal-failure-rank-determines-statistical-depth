module

public import PaperProofs.Paid.PDROC_SimulatorFlow_009

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u v
variable {I : Instance} {Seed : Type u} {OldSeed : Type v}

/-- Pure final-cursor capture from a genuine minimal last-stage exit. The
view can be the actual simulator shadow. Only the captured active exit
requires terminal-tail correctness; no virtual Prefix range is assumed. -/
theorem finalCursorHistory_eq_tailProjection_of_minimal_exit
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (actual : PolicyRule I Seed)
    (hl : LegalRule input C mode accounting actual) (sample : Seed × input.World)
    (stage : I.Stage) (hlast : stage.val + 1 = I.stageCount)
    (view : List (VisibleEvent I) → List (VisibleEvent I))
    (hcursor : ∀ clock, historyCursor (view (run input C mode accounting actual sample clock).history) =
      (run input C mode accounting actual sample clock).cursor)
    (hhalt : ∀ clock, historyHalted (view (run input C mode accounting actual sample clock).history) =
      (run input C mode accounting actual sample clock).halted)
    (tailSource : PolicyRule I OldSeed) (oldSeed : OldSeed) (exit : EntryHistory I)
    (hcatch : ∀ entry, entryHistory input C mode accounting actual stage sample = some entry →
      ∃ (start offset : ℕ),
        FirstEntryAt input C mode accounting actual stage.val start sample ∧
        (∀ k < offset, (run input C mode accounting actual sample (start + k)).halted = false ∧
          (run input C mode accounting actual sample (start + k)).cursor = stage.val) ∧
        exit = some (view (run input C mode accounting actual sample (start + offset)).history) ∧
        ((run input C mode accounting actual sample (start + offset)).halted = true ∨
          (run input C mode accounting actual sample (start + offset)).cursor = stage.val + 1))
    (htail : ∀ entry clock, entryHistory input C mode accounting actual stage sample = some entry →
      exit = some (view (run input C mode accounting actual sample clock).history) →
      (run input C mode accounting actual sample clock).halted = false →
      (run input C mode accounting actual sample clock).cursor = I.stageCount →
      (completedHistory input C mode accounting actual sample).map view =
        some (terminalCursorTail tailSource oldSeed (view (run input C mode accounting actual sample clock).history))) :
    (oldSeed, cursorCompletedNatHistory I.stageCount ((completedHistory input C mode accounting actual sample).map view)) =
      finalCursorTailProjection I.stageCount tailSource
        ((oldSeed, (entryHistory input C mode accounting actual stage sample).map view), exit) := by
  cases he : entryHistory input C mode accounting actual stage sample with
  | none =>
    have hc : cursorCompletedNatHistory I.stageCount
        ((completedHistory input C mode accounting actual sample).map view) = none := by
      cases hh : completedHistory input C mode accounting actual sample with
      | none => rfl
      | some history =>
        obtain ⟨clock, _, _, hhistory⟩ := (completedHistory_some_iff input C mode accounting actual sample history).mp hh
        have hlt := run_cursor_lt_of_no_entry input C mode accounting actual hl sample stage he clock
        have hne : historyCursor (view history) ≠ I.stageCount := by
          rw [← hhistory, hcursor]
          omega
        simp only [Option.map_some, cursorCompletedNatHistory, hne, ↓reduceIte]
    rw [hc, Option.map_none, finalCursorTailProjection_no_prior]
  | some entry =>
    obtain ⟨start, offset, hfirst, hbefore, hx, hexit⟩ := hcatch entry he
    have ha := (firstEntryAt_unborn input C mode accounting actual hl sample stage.val start hfirst).1
    by_cases hh : (run input C mode accounting actual sample (start + offset)).halted = true
    · have hcstage := halted_minimal_stage_exit_cursor input C mode accounting actual hl sample start offset stage ha hbefore hh
      have hc : cursorCompletedNatHistory I.stageCount
          ((completedHistory input C mode accounting actual sample).map view) = none := by
        rw [completedHistory_of_halted input C mode accounting actual sample (start + offset) hh, Option.map_some]
        have hne : historyCursor (view (run input C mode accounting actual sample (start + offset)).history) ≠ I.stageCount := by
          rw [hcursor, hcstage]
          omega
        simp only [cursorCompletedNatHistory, hne, ↓reduceIte]
      rw [hc, Option.map_some, hx, finalCursorTailProjection_halted I.stageCount tailSource oldSeed _ _ ((hhalt _).trans hh)]
    · have haf := Bool.eq_false_iff.mpr hh
      have hN : (run input C mode accounting actual sample (start + offset)).cursor = I.stageCount :=
        (hexit.resolve_left hh).trans hlast
      rw [htail entry (start + offset) he hx haf hN, Option.map_some, hx,
        finalCursorTailProjection_active_N I.stageCount tailSource oldSeed _ _ ((hhalt _).trans haf) ((hcursor _).trans hN)]

end PDROC
