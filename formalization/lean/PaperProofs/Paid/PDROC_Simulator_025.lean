module

public import PaperProofs.Paid.PDROC_Simulator_024

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- Completion preserves the same mark trace, including the none branch. -/
theorem simulatorReplay_markedCompleted {SimSeed : Type*} {ActualSeed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (actual : PolicyRule I ActualSeed) (hl : LegalRule input C mode accounting actual)
    (sample : ActualSeed × input.World)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I)) (seed : SimSeed) :
    (completedHistory input C mode accounting actual sample).map markedHistory =
      (completedHistory input C mode accounting actual sample).map
        (fun history => markedHistory (simulatorReplay draw seed history).shadow) := by
  cases hc : completedHistory input C mode accounting actual sample with
  | none => rfl
  | some history =>
    obtain ⟨n, _, _, hh⟩ := (completedHistory_some_iff input C mode accounting actual sample history).mp hc
    obtain ⟨k, _, hp⟩ := run_has_prefix input C mode accounting actual hl sample n
    have hm := simulatorReplay_markedHistory_prefix input C hearly mode accounting actual
      sample.1 _ _ hp draw seed
    have hhistory : markedHistory history = markedHistory (simulatorReplay draw seed history).shadow := by
      simpa only [hh] using hm
    exact congrArg some hhistory

/-- Every sample of the concrete actual policy has precisely the virtual
marked completion. No law, return, or expected-fee premise is used. -/
theorem simulator_markedCompletedHistory
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type*} [MeasurableSpace SourceSeed]
    (source : Policy (P.input fee hfee) C.val .uncapped accounting SourceSeed)
    (sample : SimulatorSeed P SourceSeed × (P.input fee hfee).World) :
    (completedHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorPolicy P fee hfee C accounting source).rule sample).map markedHistory =
      (P.shadowCompletedHistory fee hfee C accounting
        (simulatorPolicy P fee hfee C accounting source).rule
        (simulatorData P fee hfee source.rule) sample).map markedHistory := by
  have hm := simulatorReplay_markedCompleted (P.input fee hfee) C.val C.property.1.1 .uncapped accounting
    (simulatorPolicy P fee hfee C accounting source).rule
    (simulatorPolicy P fee hfee C accounting source).legal sample
    (simulatorSeedDraw P fee hfee source.rule) sample.1
  simpa only [PaperProofs.Paid.Parameters.shadowCompletedHistory, simulatorData, simulatorShadow,
    Option.map_map, Function.comp_def] using hm

end PDROC
