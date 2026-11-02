module

public import PaperProofs.Paid.PDROC_OverlayCoins_002
public import PaperProofs.Paid.PDROC_OverlayKernel_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

universe u

noncomputable def overlayPaidMixtureLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) : Measure (Bool × Bool) :=
  adjacentMixtureSeedLaw (overlayLocalMixtureWeight P fee hfee record)

instance overlayPaidMixtureLaw_probability (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) : IsProbabilityMeasure (overlayPaidMixtureLaw P fee hfee record) := by
  unfold overlayPaidMixtureLaw
  infer_instance

noncomputable def overlayPaidMarkLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) : Measure Bool :=
  rocCoinLaw (overlayLocalMarkWeight P fee hfee record)

instance overlayPaidMarkLaw_probability (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) : IsProbabilityMeasure (overlayPaidMarkLaw P fee hfee record) := by
  unfold overlayPaidMarkLaw
  infer_instance

noncomputable def overlayPaidStageCoinsLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    Measure OverlayStageCoins :=
  overlayStageCoinsLaw (overlayPaidMixtureLaw P fee hfee) (overlayPaidMarkLaw P fee hfee)

instance overlayPaidStageCoinsLaw_probability (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    IsProbabilityMeasure (overlayPaidStageCoinsLaw P fee hfee) := by
  unfold overlayPaidStageCoinsLaw
  infer_instance

noncomputable def overlayPaidCoinTablesLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    Measure (OverlayCoinTables P) :=
  overlayCoinTablesLaw P (overlayPaidMixtureLaw P fee hfee) (overlayPaidMarkLaw P fee hfee)

instance overlayPaidCoinTablesLaw_probability (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    IsProbabilityMeasure (overlayPaidCoinTablesLaw P fee hfee) := by
  unfold overlayPaidCoinTablesLaw
  infer_instance

theorem overlayPaidStageCoinsLaw_lookup (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) :
    (overlayPaidStageCoinsLaw P fee hfee).map (fun coins => overlayStageCoinLookup coins record) =
      (overlayPaidMixtureLaw P fee hfee record).prod (overlayPaidMarkLaw P fee hfee record) :=
  overlayStageCoinsLaw_lookup _ _ record

theorem overlayPaidCoinTablesLaw_stage (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) :
    (overlayPaidCoinTablesLaw P fee hfee).map (fun coins => coins stage) = overlayPaidStageCoinsLaw P fee hfee :=
  overlayCoinTablesLaw_stage P _ _ stage

theorem overlayPaidCoinTablesLaw_lookup (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) :
    (overlayPaidCoinTablesLaw P fee hfee).map (fun coins => overlayStageCoinLookup (coins stage) record) =
      (overlayPaidMixtureLaw P fee hfee record).prod (overlayPaidMarkLaw P fee hfee record) :=
  overlayCoinTablesLaw_lookup P _ _ stage record

/-- The original record-specific adjacent-MAP seed and false-positive mark
remain independent after an arbitrary measurable source/entry/record gate. -/
theorem overlayPaidStageCoinsLaw_selected_jointLaw {X : Type u} [MeasurableSpace X]
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (μ : Measure X)
    (select : X → AuxiliaryRecord) (hselect : Measurable select)
    (B : Set X) (hB : MeasurableSet B) (record : AuxiliaryRecord) :
    ((μ.restrict (B ∩ select ⁻¹' {record})).prod (overlayPaidStageCoinsLaw P fee hfee)).map
        (fun pair => (pair.1, overlayStageCoinLookup pair.2 (select pair.1))) =
      (μ.restrict (B ∩ select ⁻¹' {record})).prod
        ((overlayPaidMixtureLaw P fee hfee record).prod (overlayPaidMarkLaw P fee hfee record)) :=
  overlayStageCoinsLaw_selected_jointLaw μ _ _ select hselect B hB record

end PDROC

