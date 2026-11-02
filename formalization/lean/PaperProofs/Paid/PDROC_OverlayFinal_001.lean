module

public import PaperProofs.Paid.PDROC_OverlaySimulator_045
public import PaperProofs.Paid.PDROC_OverlayAssembly_004
public import PaperProofs.Paid.PDROC_OverlayAssembly_006
public import PaperProofs.Paid.PDROC_OverlayAssembly_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

/-- The exact original full concrete paid overlay representation.
All Native, probability, success, full-history and cost fields are derived
from the original source policy's finite complete expected bill. -/
theorem overlayVirtualRepresentation (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type u} [MeasurableSpace Seed]
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    OverlayDraft.VirtualOverlayRepresentation P fee hfee C accounting ν (overlaySeedLaw P fee hfee ν)
      source (overlayPolicy P fee hfee C accounting source) (overlayData P source.rule) :=
  overlay_concreteRepresentation_of_guardGood_capture P fee hfee C accounting source ν hfinite
    (fun stage sample hs hg => overlay_minimal_exit_captured P fee hfee C accounting source.rule stage sample hs hg)

/-- Original all-mode, arbitrary private-seed universe D14, retaining
the complete bill, risk, all original ENNReal penalties and nonreturn
clauses under the authoritative record-aware witness encoding. -/
theorem virtualErrorCouplingClaims (P : Parameters) : OverlayDraft.VirtualErrorCouplingClaims.{u} P := by
  apply virtualErrorCouplingClaims_of_concreteOverlay P
  intro fee hfee C accounting Seed ms
  let : MeasurableSpace Seed := ms
  intro ν hν
  let : IsProbabilityMeasure ν := hν
  intro source hfinite
  exact overlayVirtualRepresentation P fee hfee C accounting source ν hfinite

/-- Original D15 paid overlay policy for every original policy and seed
universe, with the original risk comparator and complete expected bill. -/
theorem paidOverlayPolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    P.PaidOverlayPolicy.{u} C accounting fee hfee :=
  paidOverlayPolicy_of_d14_recordAware P (virtualErrorCouplingClaims P) fee hfee C accounting

/-- Original D15 full-policy infimum, including infinite-bill branches. -/
theorem paidOverlayValue (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    P.PaidOverlayValue C accounting fee hfee :=
  paidOverlayValue_of_d14_recordAware P (virtualErrorCouplingClaims.{0} P) fee hfee C accounting

end PDROC
