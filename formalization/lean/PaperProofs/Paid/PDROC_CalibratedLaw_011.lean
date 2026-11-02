module

public import PaperProofs.Paid.PDROC_CalibratedLaw_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Statistics
open scoped ENNReal

namespace PDROC.CalibratedLaw

open PDROC.CalibratedRuntime

theorem measurable_outcomeSignature (P : Parameters) : Measurable (outcomeSignature P) :=
  measurable_of_countable _

/-- Both fixed whole-policy branches hold simultaneously outside one null
set of original seed/world pairs. Hence the original single initial bit
can select either branch without adding a return or finiteness premise. -/
theorem initialSelector_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (weight : Set.Icc (0 : ℝ) 1) (p : Bool → A × B → Prop)
    (branches : ∀ branch, ∀ᵐ pair ∂μ.prod ν, p branch pair) :
    ∀ᵐ sample ∂((BinarySymmetric.Parameters.rocCoinLaw weight).prod μ).prod ν,
      p sample.1.1 (sample.1.2, sample.2) := by
  have both : ∀ᵐ pair ∂μ.prod ν, ∀ branch, p branch pair := by
    filter_upwards [branches true, branches false] with pair ht hf branch
    cases branch
    · exact hf
    · exact ht
  have forget : MeasurePreserving (fun sample : (Bool × A) × B => (sample.1.2, sample.2))
      (((BinarySymmetric.Parameters.rocCoinLaw weight).prod μ).prod ν) (μ.prod ν) :=
    (measurePreserving_snd (μ := BinarySymmetric.Parameters.rocCoinLaw weight) (ν := μ)).prod
      (MeasurePreserving.id ν)
  filter_upwards [forget.quasiMeasurePreserving.ae both] with sample hs
  exact hs sample.1.1

theorem calibratedSelectedRecord_signature_law (P : Parameters) (tableOf : Bool → MenuTable)
    (valid : ∀ branch, TableLevelsValid P (tableOf branch))
    (weight : Set.Icc (0 : ℝ) 1) (fee : ℚ) (hfee : 0 ≤ fee) :
    ((P.input fee hfee).seededWorldLaw
      ((BinarySymmetric.Parameters.rocCoinLaw weight).prod P.calibratedMenuSeedLaw)).map
        (fun sample => outcomeSignature P (calibratedSelectedRecord P tableOf fee hfee sample).outcome) =
      ((P.input fee hfee).seededWorldLaw
        ((BinarySymmetric.Parameters.rocCoinLaw weight).prod (menuSeedLaw P.certificate.stages P.tools))).map
        (fun sample => outcomeSignature P (idealSelectedRecord P tableOf fee hfee sample).outcome) := by
  have law := congrArg (fun μ : Measure Outcome => μ.map (outcomeSignature P))
    (calibratedSelectedRecord_outcome_law P tableOf valid weight fee hfee)
  rw [Measure.map_map (measurable_outcomeSignature P)
      (measurable_calibratedSelectedRecord P tableOf fee hfee).2,
    Measure.map_map (measurable_outcomeSignature P)
      (measurable_idealSelectedRecord P tableOf fee hfee).2] at law
  exact law

end PDROC.CalibratedLaw
