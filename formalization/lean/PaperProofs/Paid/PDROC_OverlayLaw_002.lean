module

public import PaperProofs.Paid.PDROC_OverlayLaw_001
public import PaperProofs.Paid.PDROC_OverlayKernel_010
public import PaperProofs.Paid.PDROC_SimulatorLaw_015

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

noncomputable def overlayEventualReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) :=
  overlayMixedSampledReportedDraw P fee hfee (sourceForOptionalHistory source) stage
    (overlayEventualStageSample P fee hfee C accounting source stage sample)

theorem measurable_overlayEventualReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (overlayEventualReportedDraw P fee hfee C accounting source stage) :=
  (measurable_overlayMixedSampledReportedDraw P fee hfee (sourceForOptionalHistory source)
    (measurable_sourceForOptionalHistory source hm) stage).comp
      (measurable_overlayEventualStageSample P fee hfee C accounting source hm stage)

theorem overlayEventualReportedDraw_law_of_entryLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
      (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage) :
    ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
      (overlayEventualReportedDraw P fee hfee C accounting source.rule stage) =
      (simulatorSourceReportedDrawLaw P 0 (by norm_num) (sourceForOptionalHistory source.rule)
        (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage
          (sourceEventualDrawSeedLaw P 0 (by norm_num) C accounting source ν stage)).map reportedDrawSome := by
  have hm := measurable_overlayMixedSampledReportedDraw P fee hfee (sourceForOptionalHistory source.rule)
    (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage
  calc
    _ = (((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
        (overlayEventualStageSample P fee hfee C accounting source.rule stage)).map
          (overlayMixedSampledReportedDraw P fee hfee (sourceForOptionalHistory source.rule) stage) :=
      (Measure.map_map hm (measurable_overlayEventualStageSample P fee hfee C accounting source.rule source.measurable_rule stage)).symm
    _ = _ := by
      rw [overlayEventualStageSample_law_of_entryLaw P fee hfee C accounting source ν stage hentry]
      exact overlayMixedSampledReportedDraw_law P fee hfee (sourceForOptionalHistory source.rule)
        (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage _
          (sourceEventualDraw_finiteET_of_fullBill P 0 (by norm_num) C accounting source ν stage hfinite)

/-- This is the concrete actual-sample guard witness used by finite-stage
flow. Its sole entry hypothesis is eliminated by stage induction. -/
theorem overlayEventualReportedDraw_guardGood_ae_of_entryLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
      (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν),
      optionalSourceDrawGuardGood (sourceForOptionalHistory source.rule) stage
        (overlayEventualReportedDraw P fee hfee C accounting source.rule stage sample) := by
  let wrapped := sourceForOptionalHistory source.rule
  let hm := measurable_sourceForOptionalHistory source.rule source.measurable_rule
  have hsource := sourceEventualReportedDraw_guardGood_ae P 0 (by norm_num) C accounting source ν stage hfinite
  have hgood : ∀ᵐ record ∂(simulatorSourceReportedDrawLaw P 0 (by norm_num) wrapped hm stage
      (sourceEventualDrawSeedLaw P 0 (by norm_num) C accounting source ν stage)).map reportedDrawSome,
      optionalSourceDrawGuardGood wrapped stage record := by
    apply (ae_map_iff measurable_reportedDrawSome.aemeasurable
      (measurableSet_optionalSourceDrawGuardGood wrapped hm stage)).mpr
    filter_upwards [hsource] with record hg
    exact ⟨record.1.2, rfl, hg⟩
  have hactual : ∀ᵐ record ∂((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
      (overlayEventualReportedDraw P fee hfee C accounting source.rule stage),
      optionalSourceDrawGuardGood wrapped stage record := by
    rw [overlayEventualReportedDraw_law_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry]
    exact hgood
  exact ae_of_ae_map
    (measurable_overlayEventualReportedDraw P fee hfee C accounting source.rule source.measurable_rule stage).aemeasurable hactual

end PDROC
