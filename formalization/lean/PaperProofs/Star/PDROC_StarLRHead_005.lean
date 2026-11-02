module

public import PaperProofs.Star.PDROC_StarLRHead_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarLRHead

theorem referenceHeadTest_bayes_charge_le (P : PaperProofs.Star.Parameters) (order : Order) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) :
    P.channel.experiment.bayesObservationCharge (Measure.dirac ()) (referenceHeadTest P order r) ≤
      ENNReal.ofReal (P.channel.a * (Real.log (1/r) + P.channel.h)) := by
  unfold PaperProofs.Statistics.BinaryExperiment.bayesObservationCharge
  calc
    _ ≤ ∑ truth : Bool, P.channel.experiment.priorMass truth *
        ENNReal.ofReal (P.channel.a * (Real.log (1/r) + P.channel.h)) := by
      apply Finset.sum_le_sum
      intro truth _
      exact mul_le_mul_right (referenceHeadTest_performance P order hr hrhalf truth).2.2 _
    _ = _ := by rw [← Finset.sum_mul, P.channel.experiment.priorMass_sum, one_mul]

theorem referenceHeadTest_error_world_le (P : PaperProofs.Star.Parameters) (order : Order) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) :
    (∫⁻ sample : Unit × (P.input order).World,
      (if (referenceHeadTest P order r).rule.decision sample.1
          ((P.input order).reviewAt sample.2 (firstStage P.tools order)) ≠
        (P.input order).truthAt sample.2 (firstStage P.tools order) then (1 : ℝ≥0∞) else 0)
        ∂(P.input order).seededWorldLaw (Measure.dirac ())) ≤ ENNReal.ofReal r := by
  have law := bayesError_eq_seededWorld_integral (P.input order) (firstStage P.tools order)
    (Measure.dirac ()) (referenceHeadTest P order r)
  apply law.symm.le.trans
  unfold PaperProofs.Statistics.BinaryExperiment.bayesError
  calc
    _ ≤ ∑ truth : Bool, P.channel.experiment.priorMass truth * ENNReal.ofReal r := by
      apply Finset.sum_le_sum
      intro truth _
      exact mul_le_mul_right (referenceHeadTest_performance P order hr hrhalf truth).2.1 _
    _ = _ := by rw [← Finset.sum_mul, P.channel.experiment.priorMass_sum, one_mul]

set_option maxHeartbeats 800000 in
theorem referenceHeadTest_stop_world_ae (P : PaperProofs.Star.Parameters) (order : Order) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) :
    ∀ᵐ sample : Unit × (P.input order).World ∂(P.input order).seededWorldLaw (Measure.dirac ()),
      realPosteriorStop P.channel.experiment r
        ((P.input order).reviewAt sample.2 (firstStage P.tools order)) ≠ ⊤ := by
  let charge : Unit × (P.input order).World → ℝ≥0∞ := fun sample =>
    P.channel.experiment.observationCharge ((referenceHeadTest P order r).rule.stop sample.1
      ((P.input order).reviewAt sample.2 (firstStage P.tools order)))
  have measurableTape : Measurable (fun sample : Unit × (P.input order).World =>
      (P.input order).reviewAt sample.2 (firstStage P.tools order)) :=
    measurable_pi_iff.mpr (fun n => ((P.input order).measurable_reviewAt
      (firstStage P.tools order) n).comp measurable_snd)
  have measurableCharge : Measurable charge :=
    (measurable_of_countable P.channel.experiment.observationCharge).comp
      ((referenceHeadTest P order r).measurable_stop.comp
        (measurable_fst.prodMk measurableTape))
  have law := bayesObservationCharge_eq_seededWorld_integral (P.input order) (firstStage P.tools order)
    (Measure.dirac ()) (referenceHeadTest P order r)
  have finite : (∫⁻ sample, charge sample ∂(P.input order).seededWorldLaw (Measure.dirac ())) ≠ ⊤ := by
    have finiteBayes := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (referenceHeadTest_bayes_charge_le P order hr hrhalf)
    exact law ▸ finiteBayes
  filter_upwards [ae_lt_top measurableCharge finite] with sample finiteCharge
  intro infinite
  have stop : (referenceHeadTest P order r).rule.stop sample.1
      ((P.input order).reviewAt sample.2 (firstStage P.tools order)) = ⊤ := by
    cases sample.1
    exact (reference_head_stop P order r _).trans infinite
  change P.channel.experiment.observationCharge _ < ⊤ at finiteCharge
  rw [stop, PaperProofs.Statistics.BinaryExperiment.observationCharge_top] at finiteCharge
  exact (lt_irrefl _ finiteCharge)

end PDROC.StarLRHead
