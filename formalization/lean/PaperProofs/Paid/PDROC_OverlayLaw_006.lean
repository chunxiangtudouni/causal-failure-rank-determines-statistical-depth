module

public import PaperProofs.Paid.PDROC_OverlayLaw_005
public import PaperProofs.Paid.PDROC_OverlaySimulator_005
public import PaperProofs.Paid.PDROC_Simulator_045

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance} {SourceSeed : Type*}

/-- No permission-checked virtual correction can be inserted past the
last real stage, independently of the source's next action. -/
theorem overlayGhostCalls_terminalCursor (fuel : ℕ) (source : PolicyRule I SourceSeed)
    (seed : SourceSeed) (history : List (VisibleEvent I))
    (hc : historyCursor history = I.stageCount) : overlayGhostCalls fuel source seed history = [] := by
  have hn : overlayGhostCallOfAction history (source seed history) = none := by
    by_cases ha : historyAllowsAction history (source seed history)
    · have hcases := historyAllowsAction_terminalCursor_cases history hc (source seed history) ha
      rcases hcases with hs | hs <;> simp only [overlayGhostCallOfAction, hs, historyAllowsAction, ↓reduceIte]
    · simp only [overlayGhostCallOfAction, ha, ↓reduceIte]
  cases fuel <;> simp only [overlayGhostCalls, hn]

universe u
variable {Seed : Type u}

theorem overlaySeedGhost_terminalCursor (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (seed : OverlaySeed P Seed) (history : List (VisibleEvent P.sharedInstance))
    (hc : historyCursor history = P.sharedInstance.stageCount) :
    overlaySeedGhost P source seed (overlaySeedReplay P source seed history) = [] := by
  have hp := overlayReplay_historyProjection (overlaySeedDraw P source) (overlaySeedMark P)
    (overlaySeedGhost P source) seed history
  have hv : historyCursor (overlaySeedReplay P source seed history).shadow = P.sharedInstance.stageCount :=
    hp.1.symm.trans hc
  unfold overlaySeedGhost overlayGhostAtCache
  split
  · rfl
  · exact overlayGhostCalls_terminalCursor 2 source seed.1 _ hv

theorem overlayShadow_terminal_outOfRange (P : Parameters) (source : PolicyRule P.sharedInstance Seed)
    (seed : OverlaySeed P Seed) (history : List (VisibleEvent P.sharedInstance)) (abandoned : Bool)
    (hc : historyCursor history = P.sharedInstance.stageCount) :
    overlayShadow P source seed (history ++ [if abandoned then .abandoned else .stopped]) =
      overlayShadow P source seed history ++ [if abandoned then .abandoned else .stopped] := by
  have hn : ¬ historyCursor (overlaySeedReplay P source seed history).seen < P.sharedInstance.stageCount := by
    change ¬ historyCursor (overlayReplay (overlaySeedDraw P source) (overlaySeedMark P)
      (overlaySeedGhost P source) seed history).seen < P.sharedInstance.stageCount
    rw [overlayReplay_seen, hc]
    exact Nat.lt_irrefl _
  have hg := overlaySeedGhost_terminalCursor P source seed history hc
  change (overlayReplay (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) seed
    (history ++ [if abandoned then .abandoned else .stopped])).shadow = _
  cases abandoned <;>
    simp only [Bool.false_eq_true, ↓reduceIte, overlayReplay_append_event, overlayStep,
      show ¬ historyCursor (overlayReplay (overlaySeedDraw P source) (overlaySeedMark P)
        (overlaySeedGhost P source) seed history).seen < P.sharedInstance.stageCount from hn,
      ↓reduceDIte, show overlaySeedGhost P source seed
        (overlayReplay (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) seed history) = [] from hg,
      overlayGhostEvents, List.map_nil, List.nil_append, simulatorAppend]
  all_goals rfl

theorem overlayRule_terminalCursor_of_historyAllowsAction
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed)
    (history : List (VisibleEvent P.sharedInstance))
    (hh : historyHalted history = false) (hc : historyCursor history = P.sharedInstance.stageCount)
    (hallow : historyAllowsAction (overlayShadow P source seed history)
      (source seed.1 (overlayShadow P source seed history))) :
    overlayRule P fee hfee source seed history = source seed.1 (overlayShadow P source seed history) := by
  have hp := overlayReplay_historyProjection (overlaySeedDraw P source) (overlaySeedMark P)
    (overlaySeedGhost P source) seed history
  have hv : historyCursor (overlayShadow P source seed history) = P.sharedInstance.stageCount := hp.1.symm.trans hc
  have hcases := historyAllowsAction_terminalCursor_cases _ hv _ hallow
  have hn : ¬ historyCursor history < P.sharedInstance.compatibility.length := by
    rw [hc]
    exact Nat.lt_irrefl _
  have hstage : simulatorStageAt history = none := by
    simp only [simulatorStageAt, hn, ↓reduceDIte]
  have hg := overlaySeedGhost_terminalCursor P source seed history hc
  have hcand : overlayCandidate P fee hfee source seed history =
      reserialAction history (fun _ bit => bit) (source seed.1 (overlayShadow P source seed history)) := by
    simp only [overlayCandidate, overlayCandidateAtCache, hh, Bool.false_eq_true, ↓reduceIte, hstage,
      overlayPostwriteAction, hg, overlayGhostEvents, List.map_nil, List.append_nil, overlayShadow]
  rcases hcases with hs | hs
  · simp only [overlayRule, hcand, hs, reserialAction, historyAllowsAction, ↓reduceIte]
  · simp only [overlayRule, hcand, hs, reserialAction, historyAllowsAction, ↓reduceIte]

/-- At cursor N the actual completed shadow is precisely the measurable
source stop/abandon tail. Only the public active-history permission is
needed; no source-history law or source reachability is assumed. -/
theorem overlay_terminalCursor_shadowCompletedHistory
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) (start : ℕ)
    (hc : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source)
      sample start).cursor = P.sharedInstance.stageCount)
    (hallow : historyHalted (overlayShadow P source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).history) = false →
      historyAllowsAction (overlayShadow P source sample.1
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).history)
        (source sample.1.1 (overlayShadow P source sample.1
          (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).history))) :
    P.shadowCompletedHistory fee hfee C accounting (overlayRule P fee hfee source)
      (overlayData P source).toRecordSimulatorData sample =
      some (terminalCursorTail source sample.1.1 (overlayShadow P source sample.1
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).history)) := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  let history := (run input C.val .uncapped accounting actual sample start).history
  have hl := overlayRule_legal P fee hfee C accounting source
  obtain ⟨an, _, ap⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample start
  have hcursor : historyCursor history = P.sharedInstance.stageCount :=
    (prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ ap).trans hc
  have hp := overlayReplay_historyProjection (overlaySeedDraw P source) (overlaySeedMark P)
    (overlaySeedGhost P source) sample.1 history
  have hcShadow : historyCursor (overlayShadow P source sample.1 history) = P.sharedInstance.stageCount :=
    hp.1.symm.trans hcursor
  have hcompletion := terminalCursorTail_eq_completedHistory input C.val C.property .uncapped accounting actual hl sample start hc
  change (completedHistory input C.val .uncapped accounting actual sample).map (overlayShadow P source sample.1) = _
  rw [hcompletion]
  simp only [Option.map_some]
  apply congrArg some
  change overlayShadow P source sample.1 (terminalCursorTail actual sample.1 history) =
    terminalCursorTail source sample.1.1 (overlayShadow P source sample.1 history)
  by_cases hh : historyHalted history = true
  · have hvh : historyHalted (overlayShadow P source sample.1 history) = true := hp.2.2.symm.trans hh
    simp only [terminalCursorTail, hh, hvh, ↓reduceIte]
  · have ha : historyHalted history = false := Bool.eq_false_iff.mpr hh
    have hva : historyHalted (overlayShadow P source sample.1 history) = false := hp.2.2.symm.trans ha
    have hvallow := hallow hva
    have heq : actual sample.1 history = source sample.1.1 (overlayShadow P source sample.1 history) :=
      overlayRule_terminalCursor_of_historyAllowsAction P fee hfee source sample.1 history ha hcursor hvallow
    have hcases := historyAllowsAction_terminalCursor_cases _ hcShadow _ hvallow
    simp only [terminalCursorTail, ha, hva, Bool.false_eq_true, ↓reduceIte, heq]
    rcases hcases with hs | hs
    · rw [hs]
      simpa only [postwriteResponse, Bool.false_eq_true, ↓reduceIte] using
        overlayShadow_terminal_outOfRange P source sample.1 history false hcursor
    · rw [hs]
      simpa only [postwriteResponse, ↓reduceIte] using
        overlayShadow_terminal_outOfRange P source sample.1 history true hcursor

end PDROC
