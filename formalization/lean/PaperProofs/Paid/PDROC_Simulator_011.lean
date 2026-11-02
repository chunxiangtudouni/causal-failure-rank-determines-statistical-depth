module

public import PaperProofs.Paid.PDROC_Simulator_009

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

theorem simulatorRule_after_observations_eq_boundary (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed)
    (seed : SimulatorSeed P Seed) (entry : List (VisibleEvent P.sharedInstance))
    (stage : P.sharedInstance.Stage) (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hh : historyHalted entry = false) (hc : historyCursor entry = stage.val)
    (hw : historyWritten entry stage = none)
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed entry) = some draw)
    (hd : draw.record.decision = some decision) (letters : List (Fin 2)) :
    simulatorRule P fee hfee source seed (entry ++ letters.map (fun symbol => .observation stage symbol.val)) =
      simulatorBoundaryAction (entry ++ letters.map (fun symbol => .observation stage symbol.val)) stage draw.record (seed.2.2 stage) := by
  have hdraw' : simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed (entry ++ letters.map (fun symbol => .observation stage symbol.val))) = some draw :=
    (congrArg (simulatorSeedDraw P fee hfee source seed stage)
      (simulatorShadow_append_observations P fee hfee source seed entry stage letters)).trans hdraw
  exact simulatorRule_prewrite_some P fee hfee source seed _ stage draw decision
    ((historyHalted_append_observations entry stage letters).trans hh)
    ((historyCursor_append_observations entry stage letters).trans hc)
    ((historyWritten_append_observations entry stage stage letters).trans hw) hdraw' hd

/-- The real controller writes at the exact finite stop of the original
endpoint experiment, including the independent zero-level fair guess. -/
theorem simulatorRule_on_endpoint_word_at_stop (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed)
    (seed : SimulatorSeed P Seed) (entry : List (VisibleEvent P.sharedInstance))
    (stage : P.sharedInstance.Stage) (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hh : historyHalted entry = false) (hc : historyCursor entry = stage.val)
    (hw : historyWritten entry stage = none) (ho : historyObservations entry stage = [])
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed entry) = some draw)
    (hd : draw.record.decision = some decision) (tape : P.binarySymmetric.experiment.Tape) (n : ℕ)
    (hs : (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage) tape = (n : ℕ∞)) :
    simulatorRule P fee hfee source seed (entry ++ headReviewHistory (P.input fee hfee) stage tape n) =
      .write stage (Bool.xor decision (Bool.xor draw.record.orientation
        ((P.binarySymmetric.rocEndpointTest draw.record.level).rule.decision (seed.2.2 stage) tape))) := by
  let letters := List.ofFn (fun k : Fin n => tape k.val)
  let history := entry ++ letters.map (fun symbol => VisibleEvent.observation stage symbol.val)
  have hword : entry ++ headReviewHistory (P.input fee hfee) stage tape n = history :=
    congrArg (List.append entry) (headReviewHistory_eq_simulatorObservations P fee hfee stage tape n)
  have hzero : simulatorObservedScore entry stage = 0 := by
    simp only [simulatorObservedScore, ho, List.map_nil, List.sum_nil]
  have hhead : simulatorObservedScore (entry ++ headReviewHistory (P.input fee hfee) stage tape n) stage =
      P.binarySymmetric.signedSum tape n := by
    simpa only [hzero, zero_add] using simulatorObservedScore_headReview P fee hfee entry stage tape n
  have hscore : simulatorObservedScore history stage = P.binarySymmetric.signedSum tape n :=
    (congrArg (fun h => simulatorObservedScore h stage) hword).symm.trans hhead
  exact (congrArg (simulatorRule P fee hfee source seed) hword).trans
    ((simulatorRule_after_observations_eq_boundary P fee hfee source seed entry stage draw decision hh hc hw hdraw hd letters).trans
      (simulatorBoundaryAction_at_endpoint P history stage draw.record (seed.2.2 stage) decision hd tape n hscore hs))

end PDROC
