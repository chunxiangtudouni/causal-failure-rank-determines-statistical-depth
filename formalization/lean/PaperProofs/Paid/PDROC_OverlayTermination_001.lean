module

public import PaperProofs.Paid.PDROC_EndpointFinite_001
public import PaperProofs.Paid.RepresentationClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

universe u

/-- The completed D06 measure-one set covers every endpoint simultaneously.
Thus ALL adjacent mixtures and record/seed/history-dependent selections
stop on that same set, without a fresh-selection or finite-ET premise. -/
theorem allOverlayTests_finite_seededWorld (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    {Seed : Type u} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      ∀ (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) (coins : Bool × Bool), ∃ n : ℕ,
        (P.overlayRecordTest fee hfee record).rule.stop coins
          (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞) := by
  filter_upwards [allEndpoints_finite_seededWorld P fee hfee ν] with sample hs
  intro stage record coins
  cases hc : coins.1
  · simpa only [PaperProofs.Paid.Parameters.overlayRecordTest, adjacentMixtureTest, hc,
      Bool.false_eq_true, ↓reduceIte] using
      hs stage (P.binarySymmetric.rocIndex (P.overlayRecordTarget fee record)
        (P.overlayRecordTarget_pos fee hfee record) + 1) coins.2
  · simpa only [PaperProofs.Paid.Parameters.overlayRecordTest, adjacentMixtureTest, hc,
      ↓reduceIte] using
      hs stage (P.binarySymmetric.rocIndex (P.overlayRecordTarget fee record)
        (P.overlayRecordTarget_pos fee hfee record)) coins.2

end PDROC
