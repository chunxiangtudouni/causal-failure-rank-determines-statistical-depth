module

public import PaperProofs.Common.NativeBellmanUpper

/-!
The original head experiment and the entire fresh continuation world have
their actual independent product law. This supplies the joint law needed
by Bellman upper integration without a posterior, Markov or finite-cost
premise and without exposing a hidden world to the policy.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

theorem bellmanHead_independent_freshSuffix (input : StatisticalInput I)
    (head : I.Stage) (hhead : head.val = 0) :
    IndepFun (fun world : input.World => world head) (input.restrictFreshWorld 1) input.worldLaw := by
  let oldHead : {i : I.Stage // i.val < 1} := ⟨head, by rw [hhead]; omega⟩
  have h := (pastViewAt_independent_fresh input 1).comp (measurable_pi_apply oldHead) measurable_id
  exact h

def bellmanHeadSeedSuffix {Seed : Type*} (input : StatisticalInput I) (head : I.Stage)
    (sample : Seed × input.World) : (Seed × input.StageSample head) × (input.freshSuffix 1).World :=
  ((sample.1, sample.2 head), input.restrictFreshWorld 1 sample.2)

theorem measurable_bellmanHeadSeedSuffix {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (head : I.Stage) :
    Measurable (bellmanHeadSeedSuffix (Seed := Seed) input head) :=
  (measurable_fst.prodMk ((measurable_pi_apply head).comp measurable_snd)).prodMk
    ((input.measurable_restrictFreshWorld 1).comp measurable_snd)

theorem bellmanHeadSeedSuffix_law {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (input.seededWorldLaw ν).map (bellmanHeadSeedSuffix input head) =
      (ν.prod (input.stageLaw head)).prod (input.freshSuffix 1).worldLaw := by
  have hheadMap : Measurable (fun world : input.World => world head) := measurable_pi_apply head
  have hfresh := input.measurable_restrictFreshWorld 1
  have hw : input.worldLaw.map (fun world => (world head, input.restrictFreshWorld 1 world)) =
      (input.stageLaw head).prod (input.freshSuffix 1).worldLaw := by
    rw [(bellmanHead_independent_freshSuffix input head hhead).map_prod_eq_prod_map_map
      hheadMap.aemeasurable hfresh.aemeasurable,
      input.worldLaw_coordinate, input.restrictFreshWorld_worldLaw]
  have hs : (input.seededWorldLaw ν).map (fun sample =>
      (sample.1, (sample.2 head, input.restrictFreshWorld 1 sample.2))) =
      ν.prod ((input.stageLaw head).prod (input.freshSuffix 1).worldLaw) := by
    rw [← hw]
    exact (Measure.map_prod_map ν input.worldLaw measurable_id (hheadMap.prodMk hfresh)).symm.trans
      (by rw [Measure.map_id])
  apply (MeasurableEquiv.prodAssoc :
    (Seed × input.StageSample head) × (input.freshSuffix 1).World ≃ᵐ
      Seed × input.StageSample head × (input.freshSuffix 1).World).map_measurableEquiv_injective
  rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable
    (measurable_bellmanHeadSeedSuffix input head), Measure.prodAssoc_prod]
  exact hs

theorem lintegral_bellmanHeadSeedSuffix {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (f : (Seed × input.StageSample head) × (input.freshSuffix 1).World → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ sample, f (bellmanHeadSeedSuffix input head sample) ∂input.seededWorldLaw ν) =
      ∫⁻ pair, f pair ∂(ν.prod (input.stageLaw head)).prod (input.freshSuffix 1).worldLaw := by
  rw [← bellmanHeadSeedSuffix_law input head hhead ν]
  exact (lintegral_map hf (measurable_bellmanHeadSeedSuffix input head)).symm

end PaperProofs.Common.Native
