module

public import PaperProofs.Star.RootStarOverflow_013
public import PaperProofs.Star.RootStarOverflow_010
public import PaperProofs.Star.RootStarOverflow_001
public import PaperProofs.Star.PStar_CountIdealRisk_025
public import PaperProofs.Star.PStar_UniversalIdealRisk_028
public import PaperProofs.Star.PStarLR_Complete_023

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace RootStarOverflow

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

universe u

theorem idealRisk (P : Parameters) (order : Order) (kind : PortKind)
    (C : Contract (starInstance P.tools order)) (hC : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (r : ℝ) (hr : 0 < r) (hq : r ≤ 1/4) :
    risk (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none (Seed := Unit))
      (Measure.dirac ()) ≤ ENNReal.ofReal r := by
  cases kind with
  | earlyRetained => exact PStarCountIdealRisk025.countIdealRisk P order .earlyRetained (Or.inl rfl) C hC accounting r hr hq
  | lateRetained => exact (PStarLR.lateRetainedConstruction P order C hC accounting r hr hq).2.1
  | current =>
    cases order with
    | singletonsFirst => exact PStarCountIdealRisk025.countIdealRisk P .singletonsFirst .current (Or.inr ⟨rfl,rfl⟩) C hC accounting r hr hq
    | universalFirst => exact PStarUniversalIdealRisk028.universalFirstIdealRisk P C hC accounting r hr hq

/-- Full original C11, all private-seed universes, with every risk, real
entry, quota, failed-path bill and native qualification obligation internal. -/
theorem c11Claims (P : Parameters) : P.C11Claims.{u} :=
  ⟨conditionalOverflow P, starOverflowAssembly P, sameTapeStarTruncation P,
    rationalStarImplementation P, nativeStarImplementation_of_risk P (starOverflowAssembly P) (idealRisk P)⟩

end RootStarOverflow
