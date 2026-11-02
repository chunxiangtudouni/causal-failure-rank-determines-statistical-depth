module

public import PaperProofs.Paid.PDROC_OverlaySimulator_007
public import PaperProofs.Paid.PDROC_OverlaySimulator_021
public import PaperProofs.Paid.PDROC_SimulatorLaw_009

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance} {Seed : Type*}

theorem overlayPostwriteTrace_add (source : PolicyRule I Seed) (seed : Seed) (stage : I.Stage)
    (history : List (VisibleEvent I)) (a b : ℕ) :
    postwriteStageTrace source seed stage history (a + b) =
      postwriteStageTrace source seed stage (postwriteStageTrace source seed stage history a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change postwriteStageStep source seed stage (postwriteStageTrace source seed stage history (a + b)) =
      postwriteStageStep source seed stage (postwriteStageTrace source seed stage (postwriteStageTrace source seed stage history a) b)
    exact congrArg (postwriteStageStep source seed stage) ih

theorem overlayGhostPacket_cursor (history : List (VisibleEvent I)) (calls : List (OverlayGhostCall I)) :
    historyCursor (history ++ overlayGhostEvents calls) = historyCursor history := by
  have hp := overlayHistoryProjection_ghostEvents calls
  rw [historyCursor_append, show historyCursor (overlayGhostEvents calls) = 0 from hp.1.symm, Nat.add_zero]

theorem overlayGhostPacket_halted (history : List (VisibleEvent I)) (calls : List (OverlayGhostCall I)) :
    historyHalted (history ++ overlayGhostEvents calls) = historyHalted history := by
  have hp := overlayHistoryProjection_ghostEvents calls
  rw [historyHalted_append, show historyHalted (overlayGhostEvents calls) = false from hp.2.2.symm]
  exact Bool.or_false _

/-- Every checked ghost packet is exactly a segment of the pure source
postwrite trace, at the number of genuine virtual calls it contains. -/
theorem overlayGhostTrace_postwriteTrace (source : PolicyRule I Seed) (seed : Seed) (stage : I.Stage)
    (history : List (VisibleEvent I)) (calls : List (OverlayGhostCall I))
    (ha : historyHalted history = false) (hc : historyCursor history = stage.val)
    (htrace : OverlayGhostTrace source seed history calls) :
    postwriteStageTrace source seed stage history calls.length = history ++ overlayGhostEvents calls := by
  induction calls generalizing history with
  | nil => simp only [List.length_nil, postwriteStageTrace, overlayGhostEvents, List.map_nil, List.append_nil]
  | cons call rest ih =>
    rcases htrace with ⟨haction, _hallow, hrest⟩
    have hstep : postwriteStageStep source seed stage history = history ++ overlayGhostEvents [call] := by
      rcases call with ⟨reserve, handle, tool⟩
      cases reserve <;>
        simp only [postwriteStageStep, ha, Bool.false_eq_true, ↓reduceIte, hc, haction,
          overlayGhostAction, postwriteResponse, overlayGhostEvents, List.map_cons, List.map_nil]
    have ha' : historyHalted (history ++ overlayGhostEvents [call]) = false :=
      (overlayGhostPacket_halted history [call]).trans ha
    have hc' : historyCursor (history ++ overlayGhostEvents [call]) = stage.val :=
      (overlayGhostPacket_cursor history [call]).trans hc
    rw [List.length_cons, Nat.add_comm rest.length 1, overlayPostwriteTrace_add]
    change postwriteStageTrace source seed stage (postwriteStageStep source seed stage history) rest.length = _
    rw [hstep, ih _ ha' hc' hrest]
    simp only [overlayGhostEvents, List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]

theorem overlayGhostCalls_postwriteTrace (fuel : ℕ) (source : PolicyRule I Seed) (seed : Seed) (stage : I.Stage)
    (history : List (VisibleEvent I)) (ha : historyHalted history = false)
    (hc : historyCursor history = stage.val) :
    postwriteStageTrace source seed stage history (overlayGhostCalls fuel source seed history).length =
      history ++ overlayGhostEvents (overlayGhostCalls fuel source seed history) :=
  overlayGhostTrace_postwriteTrace source seed stage history _ ha hc (overlayGhostCalls_trace fuel source seed history)

/-- Source Good permissions at the original three queries apply at the
precise source clock after the compressed ghost segment. -/
theorem overlayGhostCalls_postwriteGuard (fuel : ℕ) (source : PolicyRule I Seed) (seed : Seed) (stage : I.Stage)
    (history : List (VisibleEvent I)) (ha : historyHalted history = false)
    (hc : historyCursor history = stage.val)
    (hgood : sourcePostwriteGuardGood source seed stage history)
    (k : ℕ) (hk : (overlayGhostCalls fuel source seed history).length + k < 3)
    (ha' : historyHalted (postwriteStageTrace source seed stage
      (history ++ overlayGhostEvents (overlayGhostCalls fuel source seed history)) k) = false)
    (hc' : historyCursor (postwriteStageTrace source seed stage
      (history ++ overlayGhostEvents (overlayGhostCalls fuel source seed history)) k) = stage.val) :
    historyAllowsAction (postwriteStageTrace source seed stage
      (history ++ overlayGhostEvents (overlayGhostCalls fuel source seed history)) k)
      (source seed (postwriteStageTrace source seed stage
        (history ++ overlayGhostEvents (overlayGhostCalls fuel source seed history)) k)) := by
  have he : postwriteStageTrace source seed stage history
      ((overlayGhostCalls fuel source seed history).length + k) =
      postwriteStageTrace source seed stage
        (history ++ overlayGhostEvents (overlayGhostCalls fuel source seed history)) k := by
    rw [overlayPostwriteTrace_add, overlayGhostCalls_postwriteTrace fuel source seed stage history ha hc]
  have h := hgood _ hk (he.symm ▸ ha') (he.symm ▸ hc')
  rwa [he] at h

end PDROC
