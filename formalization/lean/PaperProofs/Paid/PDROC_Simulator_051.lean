module

public import PaperProofs.Paid.PDROC_Simulator_050
public import PaperProofs.Paid.PDROC_SimulatorLaw_015

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- Decode the measurable reported-draw Good event into precisely the
actual draw and guard hypotheses needed by real stage exit realization. -/
theorem simulator_entry_drawGood_of_eventualReportedDraw
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World)
    (hgood : optionalSourceDrawGuardGood (sourceForOptionalHistory source) stage
      (simulatorEventualReportedDraw P fee hfee C accounting source stage sample)) :
    ∀ entry, entryHistory (P.input fee hfee) C.val .uncapped accounting
        (simulatorRule P fee hfee source) stage sample = some entry →
      ∃ draw : SimulatorDraw P.sharedInstance,
        simulatorSeedDraw P fee hfee source sample.1 stage
          (simulatorShadow P fee hfee source sample.1 entry) = some draw ∧
        sourceDrawGuardGood source stage
          (((sample.1.1, simulatorShadow P fee hfee source sample.1 entry), draw),
            recordVirtualTruth P draw.record ((P.input fee hfee).truthAt sample.2 stage)
              (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage)) := by
  apply simulator_entry_drawGood_of_optional_stageSample P fee hfee C accounting source stage sample
  let s := simulatorEventualStageSample P fee hfee C accounting source stage sample
  let drawAt := simulatorDrawAt P fee hfee (sourceForOptionalHistory source) stage s.1.1.1 s.1.1.2 s.1.2
  change ∃ draw, drawAt = some draw ∧
    sourceDrawGuardGood (sourceForOptionalHistory source) stage
      ((s.1.1, draw), recordVirtualTruth P (simulatorDrawRecord drawAt) s.2.2.1 (s.2.1, s.2.2.2)) at hgood
  obtain ⟨draw, hd, hg⟩ := hgood
  refine ⟨draw, hd, ?_⟩
  simpa only [hd, simulatorDrawRecord, Option.map_some, Option.getD_some] using hg

end PDROC
