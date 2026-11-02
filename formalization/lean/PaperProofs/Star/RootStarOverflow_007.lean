module

public import PaperProofs.Star.RootStarOverflow_006
public import PaperProofs.Star.PStar_CurrentLegality_006
public import PaperProofs.Star.PStarLR_OriginalLegality_015

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory

namespace RootStarOverflow

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star
open PaperProofs.Star.Parameters

universe u

theorem star_legal_uncapped {Seed : Type u} (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order)) (hC : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) :
    LegalRule (P.input order) C .uncapped accounting (P.starReferenceRule order kind r limit (Seed := Seed)) := by
  cases kind with
  | current => exact PStarCurrentLegality006.current_legal_uncapped P order r limit C accounting
  | earlyRetained => exact PStarLR.retained_legal_uncapped P order .earlyRetained (by decide) r limit C hC.2.1 hC.2.2 accounting
  | lateRetained => exact PStarLR.retained_legal_uncapped P order .lateRetained (by decide) r limit C hC.2.1 hC.2.2 accounting

theorem conditionalOverflow (P : Parameters) : P.ConditionalOverflow.{u} := by
  intro order kind C hC accounting delta exponent hd hq he Seed m
  let : MeasurableSpace Seed := m
  intro nu hnu
  let : IsProbabilityMeasure nu := hnu
  intro stage truth gate hgate
  exact entry_overflow_le P order kind C accounting delta exponent hd hq he
    (star_legal_uncapped P order kind (delta / 2) none C hC accounting) nu stage truth gate hgate

end RootStarOverflow
