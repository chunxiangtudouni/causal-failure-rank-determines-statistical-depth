module

public import PaperProofs.Paid.PDROC_Simulator_044
public import PaperProofs.Paid.PDROC_TerminalTail_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem historyAllowsAction_terminalCursor_cases (history : List (VisibleEvent I))
    (hc : historyCursor history = I.stageCount) (action : Action I)
    (hallow : historyAllowsAction history action) : action = .stop ∨ action = .abandon := by
  cases action with
  | review stage | write stage bit | advance stage =>
    have hh := hallow.1
    have hi := stage.isLt
    change stage.val < I.stageCount at hi
    omega
  | allocate handle tool | execute handle tool =>
    have hh := hallow.1
    have hi := handle.stage.isLt
    change handle.stage.val < I.stageCount at hi
    omega
  | stop => exact Or.inl rfl
  | abandon => exact Or.inr rfl

theorem simulatorReplay_terminal_outOfRange {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (abandoned : Bool)
    (hc : historyCursor history = I.stageCount) :
    (simulatorReplay draw seed (history ++ [if abandoned then .abandoned else .stopped])).shadow =
      (simulatorReplay draw seed history).shadow ++ [if abandoned then .abandoned else .stopped] := by
  have hnot : ¬ historyCursor (simulatorReplay draw seed history).seen < I.stageCount := by
    rw [simulatorReplay_seen, hc]
    exact Nat.lt_irrefl _
  cases abandoned <;>
    simp only [Bool.false_eq_true, ↓reduceIte, simulatorReplay_append_event, simulatorStep, simulatorAppend]
  all_goals split_ifs
  all_goals rfl

universe u
variable {Seed : Type u}

/-- At the final cursor the pure source guard permits precisely its actual
terminal action, including when the stage count is zero. -/
theorem simulatorRule_terminalCursor_of_historyAllowsAction
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed)
    (history : List (VisibleEvent P.sharedInstance))
    (hh : historyHalted history = false) (hc : historyCursor history = P.sharedInstance.stageCount)
    (hallow : historyAllowsAction (simulatorShadow P fee hfee source seed history)
      (source seed.1 (simulatorShadow P fee hfee source seed history))) :
    simulatorRule P fee hfee source seed history = source seed.1 (simulatorShadow P fee hfee source seed history) := by
  have hproj := simulatorReplay_sameProjection (simulatorSeedDraw P fee hfee source) seed history
  have hvc : historyCursor (simulatorShadow P fee hfee source seed history) = P.sharedInstance.stageCount :=
    hproj.1.symm.trans hc
  have hcases := historyAllowsAction_terminalCursor_cases _ hvc _ hallow
  have hnot : ¬ historyCursor history < P.sharedInstance.compatibility.length := by
    rw [hc]
    exact Nat.lt_irrefl _
  have hstage : simulatorStageAt history = none := by
    simp only [simulatorStageAt, hnot, ↓reduceDIte]
  have hcand : simulatorCandidate P fee hfee source seed history =
      reserialAction history (fun _ bit => bit) (source seed.1 (simulatorShadow P fee hfee source seed history)) := by
    simp only [simulatorCandidate, simulatorCandidateAtCache, simulatorCandidateFromData, hh,
      Bool.false_eq_true, ↓reduceIte, hstage, simulatorShadow]
  rcases hcases with hs | ha
  · simp only [simulatorRule, hcand, hs, reserialAction, historyAllowsAction, ↓reduceIte]
  · simp only [simulatorRule, hcand, ha, reserialAction, historyAllowsAction, ↓reduceIte]

end PDROC
