module

public import PaperProofs.Paid.PDROC_OverlayGhostExit_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u}

theorem overlayPostwriteTrace_of_wrong_cursor (source : PolicyRule I Seed) (seed : Seed)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (hc : historyCursor history ≠ stage.val) (n : ℕ) :
    postwriteStageTrace source seed stage history n = history := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [postwriteStageTrace, ih]
    unfold postwriteStageStep
    by_cases hh : historyHalted history = true
    · rw [ite_eq_left hh]
    · rw [ite_eq_right hh, ite_eq_right hc]

theorem overlayPostwriteTrace_exit_response (source : PolicyRule I Seed) (seed : Seed)
    (stage : I.Stage) (history : List (VisibleEvent I)) (n : ℕ) (hn : 0 < n)
    (ha : historyHalted history = false) (hc : historyCursor history = stage.val)
    (hexit : source seed history = .advance stage ∨ source seed history = .stop ∨
      source seed history = .abandon) :
    postwriteStageTrace source seed stage history n = history ++ postwriteResponse (source seed history) := by
  cases n with
  | zero => omega
  | succ k =>
    have htrace : postwriteStageTrace source seed stage history (k + 1) =
        postwriteStageTrace source seed stage (postwriteStageTrace source seed stage history 1) k := by
      calc
        _ = postwriteStageTrace source seed stage history (1 + k) :=
          congrArg (postwriteStageTrace source seed stage history) (Nat.add_comm k 1)
        _ = _ := overlayPostwriteTrace_add source seed stage history 1 k
    rw [htrace]
    change postwriteStageTrace source seed stage (postwriteStageStep source seed stage history) k = _
    have hstep : postwriteStageStep source seed stage history =
        history ++ postwriteResponse (source seed history) := by
      simp [postwriteStageStep, ha, hc]
    rw [hstep]
    rcases hexit with hadvance | hstop | habandon
    · apply overlayPostwriteTrace_of_wrong_cursor
      rw [hadvance]
      change historyCursor (history ++ [.advanced stage]) ≠ stage.val
      rw [historyCursor_append, hc]
      change stage.val + 1 ≠ stage.val
      omega
    · apply postwriteStageTrace_of_halted
      rw [hstop]
      change historyHalted (history ++ [.stopped]) = true
      rw [historyHalted_append]
      cases historyHalted history <;> rfl
    · apply postwriteStageTrace_of_halted
      rw [habandon]
      change historyHalted (history ++ [.abandoned]) = true
      rw [historyHalted_append]
      cases historyHalted history <;> rfl

/-- The original full three-query postwrite trace is exactly the checked
ghost packet followed by its source exit response. This is pure history
algebra and retains the complete visible trace. -/
theorem overlayGhostCalls_two_postwriteTrace_three (source : PolicyRule I Seed) (seed : Seed)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (ha : historyHalted history = false) (hc : historyCursor history = stage.val)
    (hw : historyWritten history stage ≠ none)
    (hfresh : ∀ pair ∈ historyCommitments history, pair.1.stage ≠ stage)
    (hgood : sourcePostwriteGuardGood source seed stage history) :
    postwriteStageTrace source seed stage history 3 =
      (history ++ overlayGhostEvents (overlayGhostCalls 2 source seed history)) ++
        postwriteResponse (source seed (history ++ overlayGhostEvents (overlayGhostCalls 2 source seed history))) := by
  let calls := overlayGhostCalls 2 source seed history
  let final := history ++ overlayGhostEvents calls
  have hlen : calls.length ≤ 2 := overlayGhostCalls_length_le 2 source seed history
  have htrace := overlayPostwriteTrace_add source seed stage history calls.length (3 - calls.length)
  rw [show calls.length + (3 - calls.length) = 3 by omega] at htrace
  rw [overlayGhostCalls_postwriteTrace 2 source seed stage history ha hc] at htrace
  exact htrace.trans (overlayPostwriteTrace_exit_response source seed stage final (3 - calls.length)
    (by omega) ((overlayGhostPacket_halted history calls).trans ha)
    ((overlayGhostPacket_cursor history calls).trans hc)
    (overlayGhostCalls_two_source_exit source seed stage history ha hc hw hfresh hgood))

end PDROC
