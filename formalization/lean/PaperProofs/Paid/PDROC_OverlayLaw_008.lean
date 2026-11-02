module

public import PaperProofs.Paid.PDROC_OverlayFlow_001
public import PaperProofs.Paid.PDROC_OverlayTermination_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- All global joint-law composition is discharged once the actual
minimal capture is available at the current induction entry law. -/
theorem overlaySourceHistoryLaw_of_entrywise_minimal_capture
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hcapture : ∀ stage : P.sharedInstance.Stage,
      (((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
        (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
          sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage) →
      ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν),
        OverlayMinimalExitCaptured P fee hfee C accounting source.rule stage sample) :
    P.SourceHistoryLaw 0 (by norm_num) fee hfee C accounting ν (overlaySeedLaw P fee hfee ν) source.rule
      (overlayRule P fee hfee source.rule) (overlayData P source.rule).toRecordSimulatorData := by
  have hflow : ∀ stage next : P.sharedInstance.Stage, next.val = stage.val + 1 →
      (((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
        (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
          sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage) →
      ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν),
        overlayVirtualEntryGate P fee hfee C accounting source.rule next sample =
          simulatorNextEntryOptionalProjection next
            (overlayEventualStageExit P fee hfee C accounting source.rule stage sample) := by
    intro stage next hnext hentry
    exact overlayVirtualEntryGate_next_ae_of_minimal_exit P fee hfee C accounting source.rule
      (overlaySeedLaw P fee hfee ν) stage next hnext (hcapture stage hentry)
  have hentry := overlayVirtualEntryGate_all_law_of_next_flow P fee hfee C accounting source ν hfinite hflow
  exact overlaySourceHistoryLaw_of_entryLaws_and_minimal_captures P fee hfee C accounting source ν hfinite hentry
    (fun stage => hcapture stage (hentry stage))

/-- Probability, freshness, optional-entry flow, source local ET, all
terminal restrictions and complete SourceHistoryLaw reduce to one pure
native minimal-exit statement on the exact reported-draw Good event.
That native statement remains an explicit helper input here. -/
theorem overlaySourceHistoryLaw_of_guardGood_minimal_capture
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hnative : ∀ (stage : P.sharedInstance.Stage)
      (sample : OverlaySeed P Seed × (P.input fee hfee).World),
      (∀ (record : AuxiliaryRecord) (coins : Bool × Bool), ∃ n : ℕ,
        (P.overlayRecordTest fee hfee record).rule.stop coins
          (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞)) →
      optionalSourceDrawGuardGood (sourceForOptionalHistory source.rule) stage
        (overlayEventualReportedDraw P fee hfee C accounting source.rule stage sample) →
      OverlayMinimalExitCaptured P fee hfee C accounting source.rule stage sample) :
    P.SourceHistoryLaw 0 (by norm_num) fee hfee C accounting ν (overlaySeedLaw P fee hfee ν) source.rule
      (overlayRule P fee hfee source.rule) (overlayData P source.rule).toRecordSimulatorData := by
  apply overlaySourceHistoryLaw_of_entrywise_minimal_capture P fee hfee C accounting source ν hfinite
  intro stage hentry
  filter_upwards [allOverlayTests_finite_seededWorld P fee hfee (overlaySeedLaw P fee hfee ν),
    overlayEventualReportedDraw_guardGood_ae_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry]
    with sample hs hg
  exact hnative stage sample (hs stage) hg

end PDROC
