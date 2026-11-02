module

public import PaperProofs.Paid.PDROC_Simulator_051

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Concrete actual terminal capture under the current entry law. The
visible Good event comes from the original full source bill; actual
endpoint finiteness is the unconditional simultaneous endpoint theorem.
No range-measurability or source-world existence event is conditioned on. -/
theorem simulator_cursorCompleted_eq_terminalExit_ae_of_entryLaw
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν),
      cursorCompletedHistory stage
          (P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source.rule)
            (simulatorData P fee hfee source.rule) sample) =
        terminalExitHistory stage (simulatorVirtualEntry P fee hfee C accounting source.rule stage sample)
          (simulatorEventualStageExit P fee hfee C accounting source.rule stage sample).2 := by
  have hgood := simulatorEventualReportedDraw_guardGood_ae_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry
  have hstop := allEndpoints_finite_seededWorld P fee hfee (simulatorSeedLaw P ν)
  filter_upwards [hgood, hstop] with sample hg hs
  exact simulator_cursorCompleted_eq_terminalExit_pointwise P fee hfee C accounting source.rule stage sample (hs stage)
    (simulator_entry_drawGood_of_eventualReportedDraw P fee hfee C accounting source.rule stage sample hg)

/-- Joint old-seed × cursor-completed capture for the EXACT full raw exit
RV used in the global finite-stage law. All terminal failure marks and
full histories are retained. -/
theorem simulator_terminalCapture_ae_of_entryLaw
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν),
      cursorCompletedProjection stage
          (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source.rule)
            (simulatorData P fee hfee source.rule) sample) =
        terminalExitProjection stage (simulatorEventualStageExit P fee hfee C accounting source.rule stage sample) := by
  filter_upwards [simulator_cursorCompleted_eq_terminalExit_ae_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry]
    with sample hc
  simp only [cursorCompletedProjection, terminalExitProjection, simulatorEventualStageExit_prior, simulatorVirtualEntryGate]
  exact congrArg (Prod.mk sample.1.1) hc

end PDROC
