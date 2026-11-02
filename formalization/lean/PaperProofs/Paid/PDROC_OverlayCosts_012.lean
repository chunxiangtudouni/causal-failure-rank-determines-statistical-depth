module

public import PaperProofs.Paid.PDROC_OverlayCosts_011

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u v

/-- Complete conditional D14 assembly: every cost, nonreturn and risk field
is derived. The remaining inputs are exactly the measurable Native data,
source/record laws, real stage/path coupling, and prefix success domination.
This does not assert existence of those inputs or close the original goal. -/
theorem overlay_representation_of_components
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) [IsProbabilityMeasure νsource]
    (νactual : Measure SimSeed) [IsProbabilityMeasure νactual]
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : OverlayDraft.OverlaySimulatorData P.sharedInstance SourceSeed SimSeed)
    (hm : OverlayDraft.OverlaySimulatorMeasurable data)
    (hcausal : P.ShadowCausal data.toRecordSimulatorData)
    (halign : P.SourceRecordAlignment fee hfee C accounting νactual actual.rule data.toRecordSimulatorData)
    (hlaw : P.SourceHistoryLaw 0 (by norm_num) fee hfee C accounting νsource νactual source.rule actual.rule data.toRecordSimulatorData)
    (hstage : OverlayDraft.OverlayStageRealization P fee hfee C accounting νactual actual.rule data)
    (hpath : OverlayDraft.OverlayPathCoupling P fee hfee C accounting actual.rule data)
    (hcells : OverlayDraft.OverlayRecordCells P fee hfee C accounting νactual actual.rule data)
    (hdom : ∀ sample n,
      let virtual := data.shadow sample.1 (run (P.input fee hfee) C.val .uncapped accounting actual.rule sample n).history
      (.stopped ∈ virtual ∧ ∀ stage, PaperProofs.Paid.Parameters.historyStageResolved P.sharedInstance virtual stage = true) →
        runSuccess (P.input fee hfee) C.val .uncapped accounting actual.rule sample)
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule νsource ≠ ⊤) :
    OverlayDraft.VirtualOverlayRepresentation P fee hfee C accounting νsource νactual source actual data := by
  have hnone := overlay_completedHistory_none_zero_of_sourceHistoryLaw P fee hfee C accounting νsource νactual source actual
    data.toRecordSimulatorData hm.1 hlaw hfinite
  have hobs := overlay_expectedObservationBill_le P fee hfee C accounting νsource νactual source actual data
    hm.1 halign hlaw hstage hcells hfinite
  have hcorr := overlay_expectedActualCorrectionBill_le P fee hfee C accounting νactual actual data hstage hcells
  have hrisk := overlay_risk_le_of_prefix_success_domination P fee hfee C accounting νsource νactual source actual
    data.toRecordSimulatorData hm.1 hlaw hdom
  have hbill := overlay_fullBill_le_of_components P fee hfee C accounting νsource νactual source actual hobs hcorr
  exact ⟨hm, hcausal, halign, hlaw, hstage, hpath, hcells, hnone, hdom, hrisk, hobs, hcorr, hbill⟩

end PDROC
