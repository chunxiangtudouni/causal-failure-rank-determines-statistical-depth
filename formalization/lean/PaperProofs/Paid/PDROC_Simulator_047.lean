module

public import PaperProofs.Paid.PDROC_Simulator_046
public import PaperProofs.Paid.PDROC_SimulatorLaw_014
public import PaperProofs.Paid.PDROC_TerminalCapture_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u}

theorem simulator_sourceDrawStageExit_optionalHistory_some (source : PolicyRule I Seed) (stage : I.Stage)
    (seed : Seed) (history entry : List (VisibleEvent I)) (draw : SimulatorDraw I) (truth : Bool) :
    sourceDrawStageExit (sourceForOptionalHistory source) stage ((((seed, some history), entry), draw), truth) =
      ((seed, some history), (sourceDrawStageExit source stage (((seed, entry), draw), truth)).2) := by
  unfold sourceDrawStageExit
  apply congrArg (Prod.mk (seed, some history))
  exact postwriteStageTrace_congr_seed_rule (sourceForOptionalHistory source) source
    (seed, some history) seed (fun _ => rfl) stage _ 3

theorem simulatorEventualStageExit_prior
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World) :
    (simulatorEventualStageExit P fee hfee C accounting source stage sample).1 =
      simulatorVirtualEntryGate P fee hfee C accounting source stage sample := by
  rfl

theorem simulatorEventualStageSample_of_entry
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World)
    (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) stage sample = some entry) :
    simulatorEventualStageSample P fee hfee C accounting source stage sample =
      (((((sample.1.1, some (simulatorShadow P fee hfee source sample.1 entry)),
        simulatorShadow P fee hfee source sample.1 entry), sample.1.2.1 stage)),
        (sample.1.2.2 stage, sample.2 stage)) := by
  simp only [simulatorEventualStageSample, sourceEventualHistorySeed, simulatorVirtualEntryGate,
    simulatorVirtualEntry, he, Option.map_some, Option.getD_some]
  rfl

/-- On a genuine actual entry and selected finite draw, mixture's exact
eventual-exit RV is the source kernel on the real shadow entry. -/
theorem simulatorEventualStageExit_of_entry_draw
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World)
    (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) stage sample = some entry)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : simulatorSeedDraw P fee hfee source sample.1 stage
      (simulatorShadow P fee hfee source sample.1 entry) = some draw) :
    simulatorEventualStageExit P fee hfee C accounting source stage sample =
      ((sample.1.1, some (simulatorShadow P fee hfee source sample.1 entry)),
        some (sourceDrawStageExit source stage
          (((sample.1.1, simulatorShadow P fee hfee source sample.1 entry), draw),
            recordVirtualTruth P draw.record ((P.input fee hfee).truthAt sample.2 stage)
              (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage))).2) := by
  let shadow := simulatorShadow P fee hfee source sample.1 entry
  have hsample : simulatorEventualStageSample P fee hfee C accounting source stage sample =
      (((((sample.1.1, some shadow), shadow), sample.1.2.1 stage)), (sample.1.2.2 stage, sample.2 stage)) := by
    exact simulatorEventualStageSample_of_entry P fee hfee C accounting source stage sample entry he
  have hdraw : simulatorDrawAt P fee hfee (sourceForOptionalHistory source) stage
      (sample.1.1, some shadow) shadow (sample.1.2.1 stage) = some draw := by
    rw [simulatorDrawAt_optionalHistory_some]
    exact hd
  simp only [simulatorEventualStageExit, hsample, simulatorMixedSampledStageExit,
    simulatorSampledStageExit, hdraw, simulatorOptionalStageExit, coupledRecordTruth,
    sourceOptionalDrawStageExit, simulatorDrawRecord, Option.map_some, Option.getD_some]
  rw [simulator_sourceDrawStageExit_optionalHistory_some]
  rfl

end PDROC
