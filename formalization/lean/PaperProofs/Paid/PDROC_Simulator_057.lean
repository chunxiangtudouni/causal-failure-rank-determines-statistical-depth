module

public import PaperProofs.Paid.PDROC_Simulator_056

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The concrete ACTUAL final-cursor component is captured by the shared
measurable source-tail projection of the exact full exit RV. Its support
comes only from the original complete source bill and current entry law. -/
theorem simulator_finalCursorTail_capture_ae_of_entryLaw
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hlast : stage.val + 1 = P.sharedInstance.stageCount)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν),
      cursorCompletedNatProjection P.sharedInstance.stageCount
          (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (simulatorPolicy P fee hfee C accounting source).rule
            (simulatorData P fee hfee source.rule) sample) =
        finalCursorTailProjection P.sharedInstance.stageCount source.rule
          (simulatorEventualStageExit P fee hfee C accounting source.rule stage sample) := by
  have hgood := simulatorEventualReportedDraw_guardGood_ae_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry
  have htail := simulatorEventualStageExit_tailAllowed_ae_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry
  have hstop := allEndpoints_finite_seededWorld P fee hfee (simulatorSeedLaw P ν)
  filter_upwards [hgood, htail, hstop] with sample hg ht hs
  exact simulator_finalCursorTail_capture_pointwise P fee hfee C accounting source.rule stage hlast sample (hs stage) hg ht

end PDROC
