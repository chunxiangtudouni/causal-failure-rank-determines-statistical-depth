module

public import PaperProofs.Paid.PDROC_Simulator_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

theorem simulatorCandidateFromData_prewrite {I : Instance} (history : List (VisibleEvent I))
    (stage : I.Stage) (action : Action I) (draws : I.Stage → Option (SimulatorDraw I))
    (coins : I.Stage → Bool) (hh : historyHalted history = false)
    (hc : historyCursor history = stage.val) (hw : historyWritten history stage = none) :
    simulatorCandidateFromData history action draws coins = simulatorDrawAction history stage (coins stage) (draws stage) := by
  simp only [simulatorCandidateFromData, hh, Bool.false_eq_true, ↓reduceIte,
    simulatorStageAt_some history stage hc, hw]

variable {Seed : Type u}

theorem simulatorCandidate_prewrite_some (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hh : historyHalted history = false) (hc : historyCursor history = stage.val)
    (hw : historyWritten history stage = none)
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed history) = some draw)
    (hd : draw.record.decision = some decision) :
    simulatorCandidate P fee hfee source seed history = simulatorBoundaryAction history stage draw.record (seed.2.2 stage) := by
  unfold simulatorCandidate simulatorCandidateAtCache
  rw [simulatorCandidateFromData_prewrite history stage _ _ _ hh hc hw]
  change simulatorDrawAction history stage (seed.2.2 stage)
    (simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed history)) = _
  simp only [hdraw, simulatorDrawAction, hd]

/-- On every legitimate writing-record prewrite history, the guard is proved
nonbinding and the real rule executes exactly the actual integer-boundary
action. This statement imposes no MAP condition on the source record. -/
theorem simulatorRule_prewrite_some (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hh : historyHalted history = false) (hc : historyCursor history = stage.val)
    (hw : historyWritten history stage = none)
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed history) = some draw)
    (hd : draw.record.decision = some decision) :
    simulatorRule P fee hfee source seed history = simulatorBoundaryAction history stage draw.record (seed.2.2 stage) := by
  have hraw := simulatorCandidate_prewrite_some P fee hfee source seed history stage draw decision hh hc hw hdraw hd
  have hallow := simulatorBoundaryAction_allowed history stage draw.record (seed.2.2 stage) decision hd hc hw
  unfold simulatorRule
  rw [hraw, ite_eq_left hallow]

end PDROC
