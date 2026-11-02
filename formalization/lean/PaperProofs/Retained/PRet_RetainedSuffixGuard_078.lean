module

public import PaperProofs.Common.NativeBellmanGuardLift
public import PaperProofs.Retained.PRet_RetainedGuard_007

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetRetainedSuffixGuard078

open Common Common.Native GuardLift PRetRetainedGuard007

/-- Lift the EXISTING retained-aware public permissions through a clean
head prefix. Actual continuations may allocate/execute at the terminal
barrier behind the cursor; no current-only guard is substituted. -/
theorem allows_referenceSuffixJoin (I : Instance) (first : ℕ)
    (before : List (VisibleEvent I)) (after : List (VisibleEvent (I.freshSuffix first)))
    (hcursorBefore : historyCursor before = first)
    (hwriteBefore : ∀ stage, historyWrite before (I.freshStageLift first stage) = none)
    (hreportBefore : ∀ stage, historyReport before (I.freshStageLift first stage) = none)
    (hcommitBefore : historyCommitments before = []) (hexecBefore : historyExecutions before = [])
    (action : Action (I.freshSuffix first)) (hallow : allows after action) :
    allows (referenceSuffixHistoryJoin I first before after)
      (referenceSuffixActionLift I first (historyActions before).length action) := by
  have hcursor (stage : (I.freshSuffix first).Stage) (hc : historyCursor after = stage.val) :
      historyCursor (referenceSuffixHistoryJoin I first before after) = (I.freshStageLift first stage).val := by
    rw [historyCursor_referenceSuffixJoin, hcursorBefore, hc]
    rfl
  have husedBefore : historyUsed before = ∅ := by
    unfold historyUsed
    rw [hcommitBefore]
    rfl
  cases action with
  | review stage =>
    exact ⟨hcursor stage hallow.1,
      (historyWritten_referenceSuffixJoin I first before after stage (hwriteBefore stage)).trans hallow.2⟩
  | write stage bit =>
    exact ⟨hcursor stage hallow.1,
      (historyWritten_referenceSuffixJoin I first before after stage (hwriteBefore stage)).trans hallow.2⟩
  | advance stage =>
    refine ⟨hcursor stage hallow.1, ?_⟩
    rw [historyWritten_referenceSuffixJoin I first before after stage (hwriteBefore stage)]
    exact hallow.2
  | allocate handle tool =>
    obtain ⟨hvalid, hcompat, hunused, hslot⟩ := hallow
    refine ⟨replayValidHandle_referenceSuffixJoin I first before after handle
      (hwriteBefore handle.stage) (hreportBefore handle.stage) hvalid, ?_, ?_, ?_⟩
    · change tool ∈ I.eligible (I.freshStageLift first handle.stage)
      rw [← I.freshSuffix_eligible first handle.stage]
      exact hcompat
    · rw [historyUsed_referenceSuffixJoin]
      change (show I.Tool from tool) ∉
        (historyUsed before ∪ (show Finset I.Tool from historyUsed (I := I.freshSuffix first) after))
      rw [husedBefore, Finset.empty_union]
      exact hunused
    · intro pair hp
      rw [historyCommitments_referenceSuffixJoin, hcommitBefore, List.nil_append] at hp
      obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hp
      exact fun heq => hslot child hchild ((freshStageLift_injective I first) heq)
  | execute handle tool =>
    obtain ⟨hvalid, hcompat, hcommit, hunused, hslot⟩ := hallow
    refine ⟨replayValidHandle_referenceSuffixJoin I first before after handle
      (hwriteBefore handle.stage) (hreportBefore handle.stage) hvalid, ?_, ?_, ?_, ?_⟩
    · change tool ∈ I.eligible (I.freshStageLift first handle.stage)
      rw [← I.freshSuffix_eligible first handle.stage]
      exact hcompat
    · rw [historyCommitments_referenceSuffixJoin, hcommitBefore, List.nil_append]
      exact List.mem_map.mpr ⟨(handle, tool), hcommit, rfl⟩
    · intro pair hp
      rw [historyExecutions_referenceSuffixJoin, hexecBefore, List.nil_append] at hp
      obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hp
      exact hunused child hchild
    · intro pair hp
      rw [historyExecutions_referenceSuffixJoin, hexecBefore, List.nil_append] at hp
      obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hp
      exact fun heq => hslot child hchild ((freshStageLift_injective I first) heq)
  | stop => trivial
  | abandon => trivial

end PaperProofs.Retained.PRetRetainedSuffixGuard078
