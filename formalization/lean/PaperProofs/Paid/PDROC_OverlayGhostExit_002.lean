module

public import PaperProofs.Paid.PDROC_OverlayGhostExit_001
public import PaperProofs.Paid.PDROC_OverlayGhost_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u}

/-- On an arbitrary visible written-stage history with no current-stage
commitment, the three original source guard queries suffice to exit after
the at-most-two checked ghosts. No source world or native prefix is used. -/
theorem overlayGhostCalls_two_source_exit (source : PolicyRule I Seed) (seed : Seed)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (ha : historyHalted history = false) (hc : historyCursor history = stage.val)
    (hw : historyWritten history stage ≠ none)
    (hfresh : ∀ pair ∈ historyCommitments history, pair.1.stage ≠ stage)
    (hgood : sourcePostwriteGuardGood source seed stage history) :
    source seed (history ++ overlayGhostEvents (overlayGhostCalls 2 source seed history)) = .advance stage ∨
      source seed (history ++ overlayGhostEvents (overlayGhostCalls 2 source seed history)) = .stop ∨
      source seed (history ++ overlayGhostEvents (overlayGhostCalls 2 source seed history)) = .abandon := by
  let final := history ++ overlayGhostEvents (overlayGhostCalls 2 source seed history)
  have hfc : historyCursor final = stage.val := (overlayGhostPacket_cursor history _).trans hc
  have hfa : historyHalted final = false := (overlayGhostPacket_halted history _).trans ha
  have hfw : historyWritten final stage ≠ none := by
    intro hn
    exact hw ((historyWritten_none_append history _ stage).mp hn).1
  have hallow : historyAllowsAction final (source seed final) := by
    have hlen := overlayGhostCalls_length_le 2 source seed history
    exact overlayGhostCalls_postwriteGuard 2 source seed stage history ha hc hgood 0 (by omega) hfa hfc
  cases hfirst : overlayGhostCallOfAction history (source seed history) with
  | none =>
    have hp : overlayGhostCalls 2 source seed history = [] := by simp only [overlayGhostCalls, hfirst]
    have hn : overlayGhostCallOfAction final (source seed final) = none := by
      simpa only [final, hp, overlayGhostEvents, List.map_nil, List.append_nil] using hfirst
    exact overlay_allowed_exit_of_no_ghost final stage _ hfc hfw hallow hn
  | some first =>
    cases hsecond : overlayGhostCallOfAction (history ++ overlayGhostEvents [first])
        (source seed (history ++ overlayGhostEvents [first])) with
    | none =>
      have hp : overlayGhostCalls 2 source seed history = [first] := by
        simp only [overlayGhostCalls, hfirst, hsecond]
      have hn : overlayGhostCallOfAction final (source seed final) = none := by
        simpa only [final, hp] using hsecond
      exact overlay_allowed_exit_of_no_ghost final stage _ hfc hfw hallow hn
    | some second =>
      have hf := overlay_firstGhost_reserves_current history stage _ first hc hfresh hfirst
      have hcommit : ∃ pair ∈ historyCommitments (history ++ overlayGhostEvents [first]),
          pair.1.stage = stage := by
        refine ⟨first.2, ?_, hf.2⟩
        simp [historyCommitments, List.filterMap_append, overlayGhostEvents, hf.1, eventCommitment]
      have hs := overlay_committedGhost_executes_current (history ++ overlayGhostEvents [first])
        stage _ second ((overlayGhostPacket_cursor history [first]).trans hc) hcommit hsecond
      have hp : overlayGhostCalls 2 source seed history = [first, second] := by
        simp only [overlayGhostCalls, hfirst, hsecond]
      have hcommitFinal : ∃ pair ∈ historyCommitments final, pair.1.stage = stage := by
        refine ⟨first.2, ?_, hf.2⟩
        simp [final, hp, historyCommitments, List.filterMap_append, overlayGhostEvents, hf.1, hs.1, eventCommitment]
      have hexecuteFinal : ∃ pair ∈ historyExecutions final, pair.1.stage = stage := by
        refine ⟨second.2, ?_, hs.2⟩
        simp [final, hp, historyExecutions, List.filterMap_append, overlayGhostEvents, hf.1, hs.1, eventExecution]
      exact overlay_allowed_exit_of_committed_executed final stage _ hfc hfw hallow hcommitFinal hexecuteFinal

end PDROC

