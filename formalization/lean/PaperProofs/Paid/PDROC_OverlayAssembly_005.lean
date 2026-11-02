module

public import PaperProofs.Paid.PDROC_OverlayLaw_008
public import PaperProofs.Paid.PDROC_OverlayCells_005
public import PaperProofs.Paid.PDROC_OverlaySimulator_025
public import PaperProofs.Paid.PDROC_OverlaySimulator_030
public import PaperProofs.Paid.PDROC_OverlayCosts_012

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

/-- Concrete original representation with all probabilistic, cost,
return, freshness, complete Path/Cells and source-law components discharged. The remaining
inputs are two explicitly native path statements, not assumed
performance bounds or a supplied SourceHistoryLaw. -/
theorem overlay_concreteRepresentation_of_native_components
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type u} [MeasurableSpace Seed]
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hdom : ∀ sample n,
      let virtual := overlayShadow P source.rule sample.1
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source.rule) sample n).history
      (.stopped ∈ virtual ∧ ∀ stage, PaperProofs.Paid.Parameters.historyStageResolved P.sharedInstance virtual stage = true) →
        runSuccess (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source.rule) sample)
    (hnative : ∀ (stage : P.sharedInstance.Stage)
      (sample : OverlaySeed P Seed × (P.input fee hfee).World),
      (∀ (record : AuxiliaryRecord) (coins : Bool × Bool), ∃ n : ℕ,
        (P.overlayRecordTest fee hfee record).rule.stop coins
          (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞)) →
      optionalSourceDrawGuardGood (sourceForOptionalHistory source.rule) stage
        (overlayEventualReportedDraw P fee hfee C accounting source.rule stage sample) →
      OverlayMinimalExitCaptured P fee hfee C accounting source.rule stage sample) :
    OverlayDraft.VirtualOverlayRepresentation P fee hfee C accounting ν (overlaySeedLaw P fee hfee ν)
      source (overlayPolicy P fee hfee C accounting source) (overlayData P source.rule) := by
  have hpath := overlayPathCoupling P fee hfee C accounting source.rule
  exact overlay_representation_of_components P fee hfee C accounting ν (overlaySeedLaw P fee hfee ν)
    source (overlayPolicy P fee hfee C accounting source) (overlayData P source.rule)
    (overlayData_measurable P source.rule source.measurable_rule)
    (overlayData_shadowCausal P source.rule)
    (overlaySourceRecordAlignment P fee hfee C accounting source.rule (overlaySeedLaw P fee hfee ν))
    (overlaySourceHistoryLaw_of_guardGood_minimal_capture P fee hfee C accounting source ν hfinite hnative)
    (overlayStageRealization P fee hfee C accounting source.rule (overlaySeedLaw P fee hfee ν))
    hpath (overlayRecordCells_of_path P fee hfee C accounting source.rule source.measurable_rule ν hpath)
    hdom hfinite

end PDROC
