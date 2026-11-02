module

public import PaperProofs.Paid.PDROC_OverlayAssembly_005
public import PaperProofs.Paid.PDROC_OverlaySuccess_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

/-- Only the deterministic native Good-to-minimal-exit helper remains.
Original prefix success is discharged for every actual sample and prefix. -/
theorem overlay_concreteRepresentation_of_guardGood_capture
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type u} [MeasurableSpace Seed]
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
    OverlayDraft.VirtualOverlayRepresentation P fee hfee C accounting ν (overlaySeedLaw P fee hfee ν)
      source (overlayPolicy P fee hfee C accounting source) (overlayData P source.rule) :=
  overlay_concreteRepresentation_of_native_components P fee hfee C accounting source ν hfinite
    (overlayPolicy_prefix_success_domination P fee hfee C accounting source) hnative

end PDROC
