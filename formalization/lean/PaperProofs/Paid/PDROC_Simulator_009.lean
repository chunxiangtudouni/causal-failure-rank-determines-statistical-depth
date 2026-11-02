module

public import PaperProofs.Paid.PDROC_Simulator_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

theorem headReviewHistory_eq_simulatorObservations (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage)
    (tape : P.binarySymmetric.experiment.Tape) (n : ℕ) :
    headReviewHistory (P.input fee hfee) stage tape n =
      (List.ofFn (fun k : Fin n => tape k.val)).map (fun symbol => .observation stage symbol.val) := by
  simp only [headReviewHistory, List.map_ofFn, Function.comp_def]

/-- Exact local rule identity on every observation word before the real
endpoint stop. The selected source record is held fixed while real reviews
are read; source non-MAP decisions are preserved by the coordinate flip. -/
theorem simulatorRule_on_endpoint_word_before (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed)
    (seed : SimulatorSeed P Seed) (entry : List (VisibleEvent P.sharedInstance))
    (stage : P.sharedInstance.Stage) (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hh : historyHalted entry = false) (hc : historyCursor entry = stage.val)
    (hw : historyWritten entry stage = none) (ho : historyObservations entry stage = [])
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed entry) = some draw)
    (hd : draw.record.decision = some decision) (tape : P.binarySymmetric.experiment.Tape) (n : ℕ)
    (hbefore : (n : ℕ∞) < (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage) tape) :
    simulatorRule P fee hfee source seed (entry ++ headReviewHistory (P.input fee hfee) stage tape n) = .review stage := by
  let history := entry ++ headReviewHistory (P.input fee hfee) stage tape n
  have hh' : historyHalted history = false := by
    rw [show history = entry ++ (List.ofFn (fun k : Fin n => tape k.val)).map (fun symbol => .observation stage symbol.val) from
      congrArg (List.append entry) (headReviewHistory_eq_simulatorObservations P fee hfee stage tape n)]
    exact (historyHalted_append_observations entry stage _).trans hh
  have hc' : historyCursor history = stage.val := by
    rw [show history = entry ++ (List.ofFn (fun k : Fin n => tape k.val)).map (fun symbol => .observation stage symbol.val) from
      congrArg (List.append entry) (headReviewHistory_eq_simulatorObservations P fee hfee stage tape n)]
    exact (historyCursor_append_observations entry stage _).trans hc
  have hw' : historyWritten history stage = none := by
    rw [show history = entry ++ (List.ofFn (fun k : Fin n => tape k.val)).map (fun symbol => .observation stage symbol.val) from
      congrArg (List.append entry) (headReviewHistory_eq_simulatorObservations P fee hfee stage tape n)]
    exact (historyWritten_append_observations entry stage stage _).trans hw
  have hdraw' : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed history) = some draw := by
    have heq : simulatorShadow P fee hfee source seed history = simulatorShadow P fee hfee source seed entry :=
      (congrArg (simulatorShadow P fee hfee source seed)
        (congrArg (List.append entry) (headReviewHistory_eq_simulatorObservations P fee hfee stage tape n))).trans
        (simulatorShadow_append_observations P fee hfee source seed entry stage (List.ofFn (fun k : Fin n => tape k.val)))
    exact (congrArg (simulatorSeedDraw P fee hfee source seed stage) heq).trans hdraw
  have hzero : simulatorObservedScore entry stage = 0 := by simp only [simulatorObservedScore, ho, List.map_nil, List.sum_nil]
  have hscore : simulatorObservedScore history stage = P.binarySymmetric.signedSum tape n := by
    have h := simulatorObservedScore_headReview P fee hfee entry stage tape n
    simpa only [hzero, zero_add] using h
  rw [simulatorRule_prewrite_some P fee hfee source seed history stage draw decision hh' hc' hw' hdraw' hd]
  exact simulatorBoundaryAction_before_endpoint P history stage draw.record (seed.2.2 stage) decision hd tape n hscore hbefore

end PDROC
