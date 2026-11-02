module

public import PaperProofs.Paid.PDROC_TerminalTail_001
public import PaperProofs.Paid.PDROC_TerminalLaw_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

def cursorCompletedHistory (stage : I.Stage) : EntryHistory I → EntryHistory I
  | none => none
  | some history => if historyCursor history = stage.val then some history else none

def terminalExitHistory (stage : I.Stage) (prior exit : EntryHistory I) : EntryHistory I :=
  if prior.isSome = true then
    match exit with
    | none => none
    | some history => if historyHalted history = true ∧ historyCursor history = stage.val then some history else none
  else none

theorem cursorCompletedHistory_some_iff (stage : I.Stage) (completion : EntryHistory I)
    (history : List (VisibleEvent I)) :
    cursorCompletedHistory stage completion = some history ↔ completion = some history ∧ historyCursor history = stage.val := by
  cases completion with
  | none => simp [cursorCompletedHistory]
  | some before =>
    by_cases he : before = history
    · subst before
      simp [cursorCompletedHistory]
    · simp [cursorCompletedHistory, he]

theorem terminalExitHistory_some_iff (stage : I.Stage) (prior exit : EntryHistory I)
    (history : List (VisibleEvent I)) :
    terminalExitHistory stage prior exit = some history ↔
      prior.isSome = true ∧ exit = some history ∧ historyHalted history = true ∧ historyCursor history = stage.val := by
  cases prior with
  | none => simp [terminalExitHistory]
  | some entry =>
    cases exit with
    | none => simp [terminalExitHistory]
    | some before =>
      by_cases he : before = history
      · subst before
        simp [terminalExitHistory]
      · simp [terminalExitHistory, he]

/-- Any genuine exit capture identifies the full completed terminal
component. The view may be the concrete shadow and only needs the proved
cursor/halt projections along actual run prefixes. No source-world range
event or minimal-exit assumption is used. -/
theorem cursorCompletedHistory_eq_terminalExitHistory {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hl : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (stage : I.Stage)
    (view : List (VisibleEvent I) → List (VisibleEvent I))
    (hcursor : ∀ clock, historyCursor (view (run input C mode accounting rule sample clock).history) =
      (run input C mode accounting rule sample clock).cursor)
    (hhalt : ∀ clock, historyHalted (view (run input C mode accounting rule sample clock).history) =
      (run input C mode accounting rule sample clock).halted)
    (exit : EntryHistory I)
    (hcatch : ∀ entry, entryHistory input C mode accounting rule stage sample = some entry →
      ∃ clock, exit = some (view (run input C mode accounting rule sample clock).history) ∧
        ((run input C mode accounting rule sample clock).halted = true ∨
          stage.val < (run input C mode accounting rule sample clock).cursor)) :
    cursorCompletedHistory stage ((completedHistory input C mode accounting rule sample).map view) =
      terminalExitHistory stage ((entryHistory input C mode accounting rule stage sample).map view) exit := by
  have hiff (history : List (VisibleEvent I)) :
      cursorCompletedHistory stage ((completedHistory input C mode accounting rule sample).map view) = some history ↔
        terminalExitHistory stage ((entryHistory input C mode accounting rule stage sample).map view) exit = some history := by
    rw [cursorCompletedHistory_some_iff, terminalExitHistory_some_iff]
    constructor
    · rintro ⟨hcompletion, hfinalCursor⟩
      cases hraw : completedHistory input C mode accounting rule sample with
      | none => simp only [hraw, Option.map_none, reduceCtorEq] at hcompletion
      | some final =>
        have hview : view final = history := by simpa only [hraw, Option.map_some, Option.some.injEq] using hcompletion
        obtain ⟨n, hn, _, hh⟩ := (completedHistory_some_iff input C mode accounting rule sample final).mp hraw
        have hcn : (run input C mode accounting rule sample n).cursor = stage.val := by
          rw [← hview, ← hh] at hfinalCursor
          exact (hcursor n).symm.trans hfinalCursor
        have hentryNotNone : entryHistory input C mode accounting rule stage sample ≠ none := by
          intro he
          exact (entryHistory_none_iff input C mode accounting rule stage sample).mp he ⟨n, hcn⟩
        obtain ⟨entry, he⟩ := Option.ne_none_iff_exists'.mp hentryNotNone
        obtain ⟨clock, hx, hexit⟩ := hcatch entry he
        have hbound : (run input C mode accounting rule sample clock).cursor ≤ stage.val := by
          by_cases hclock : clock ≤ n
          · exact (run_cursor_monotone input C mode accounting rule hl sample hclock).trans hcn.le
          · have ht : clock = n + (clock - n) := by omega
            rw [ht, run_after_halt input C mode accounting rule sample n hn (clock - n), hcn]
        have hclockHalt : (run input C mode accounting rule sample clock).halted = true := by
          rcases hexit with hh | hc
          · exact hh
          · exact (Nat.not_lt_of_ge hbound hc).elim
        have hccomplete := completedHistory_of_halted input C mode accounting rule sample clock hclockHalt
        have hsame : (run input C mode accounting rule sample clock).history = final :=
          Option.some.inj (hccomplete.symm.trans hraw)
        have hxh : exit = some history := by rw [hsame, hview] at hx; exact hx
        have hhistoryHalt : historyHalted history = true := by
          rw [← hview, ← hsame]
          exact (hhalt clock).trans hclockHalt
        exact ⟨by simp only [he, Option.map_some, Option.isSome_some], hxh, hhistoryHalt, hfinalCursor⟩
    · rintro ⟨hentrySome, hx, hhistoryHalt, hhistoryCursor⟩
      have hentryNotNone : entryHistory input C mode accounting rule stage sample ≠ none := by
        intro hn
        simp only [hn, Option.map_none, Option.isSome_none, Bool.false_eq_true] at hentrySome
      obtain ⟨entry, he⟩ := Option.ne_none_iff_exists'.mp hentryNotNone
      obtain ⟨clock, hclockExit, _⟩ := hcatch entry he
      have hview : view (run input C mode accounting rule sample clock).history = history :=
        Option.some.inj (hclockExit.symm.trans hx)
      have hclockHalt : (run input C mode accounting rule sample clock).halted = true := by
        rw [← hview] at hhistoryHalt
        exact (hhalt clock).symm.trans hhistoryHalt
      have hcompletion := completedHistory_of_halted input C mode accounting rule sample clock hclockHalt
      exact ⟨by rw [hcompletion, Option.map_some, hview], hhistoryCursor⟩
  cases hf : cursorCompletedHistory stage ((completedHistory input C mode accounting rule sample).map view) with
  | none =>
    cases hg : terminalExitHistory stage ((entryHistory input C mode accounting rule stage sample).map view) exit with
    | none => rfl
    | some history =>
      have h := (hiff history).mpr hg
      rw [hf] at h
      cases h
  | some history => exact ((hiff history).mp hf).symm

def cursorCompletedProjection {Source : Type*} (stage : I.Stage) (pair : Source × EntryHistory I) : Source × EntryHistory I :=
  (pair.1, cursorCompletedHistory stage pair.2)

def terminalExitProjection {Source : Type*} (stage : I.Stage)
    (pair : (Source × EntryHistory I) × EntryHistory I) : Source × EntryHistory I :=
  (pair.1.1, terminalExitHistory stage pair.1.2 pair.2)

theorem measurable_cursorCompletedProjection {Source : Type*} [MeasurableSpace Source] (stage : I.Stage) :
    Measurable (cursorCompletedProjection (Source := Source) stage) :=
  measurable_fst.prodMk ((measurable_of_countable (cursorCompletedHistory stage)).comp measurable_snd)

theorem measurable_terminalExitProjection {Source : Type*} [MeasurableSpace Source] (stage : I.Stage) :
    Measurable (terminalExitProjection (Source := Source) stage) :=
  (measurable_fst.comp measurable_fst).prodMk
    ((measurable_of_countable (fun pair : EntryHistory I × EntryHistory I => terminalExitHistory stage pair.1 pair.2)).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

end PDROC
