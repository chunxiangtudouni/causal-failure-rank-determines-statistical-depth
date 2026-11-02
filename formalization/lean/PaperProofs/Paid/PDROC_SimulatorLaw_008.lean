module

public import PaperProofs.Paid.PDROC_SimulatorLaw_007
public import PaperProofs.Paid.PDROC_SimulatorCells_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

universe u v

/-- A common conditional full law remains common after mixing the actual
truth with its original stage prior. Both the arbitrary source coordinate
and the full output coordinate are retained. -/
theorem prod_simulatorEndpointLaw_map_of_conditional_constant
    {Source : Type u} {Target : Type v} [MeasurableSpace Source] [MeasurableSpace Target]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage)
    (ρ : Measure Source) [SFinite ρ]
    (f : Source × (Bool × (Bool × P.experiment.Tape)) → Target) (hf : Measurable f)
    (law : Measure Target)
    (hconditional : ∀ truth,
      (ρ.prod (P.binarySymmetric.experiment.conditionalLaw fairGuessLaw truth)).map
        (fun sample => f (sample.1, (sample.2.1, (truth, sample.2.2)))) = law) :
    (ρ.prod (simulatorEndpointLaw P fee hfee stage)).map f = law := by
  apply Measure.ext
  intro A hA
  let indicator := A.indicator (fun _ : Target => (1 : ℝ≥0∞))
  have hi : Measurable indicator := measurable_const.indicator hA
  have hif : Measurable (fun sample => indicator (f sample)) := hi.comp hf
  have hg : Measurable (fun endpoint : Bool × (Bool × P.experiment.Tape) =>
      ∫⁻ source, indicator (f (source, endpoint)) ∂ρ) := hif.lintegral_prod_left'
  rw [← lintegral_indicator_one hA]
  change (∫⁻ result, indicator result ∂(ρ.prod (simulatorEndpointLaw P fee hfee stage)).map f) = law A
  rw [lintegral_map hi hf, lintegral_prod_symm _ hif.aemeasurable]
  apply lintegral_simulatorEndpointLaw_of_conditional_constant P fee hfee stage _ hg
  intro truth
  have hm : Measurable (fun sample : Source × (Bool × P.experiment.Tape) =>
      f (sample.1, (sample.2.1, (truth, sample.2.2)))) :=
    hf.comp (measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_const.prodMk (measurable_snd.comp measurable_snd))))
  have ht : Measurable (fun sample : Source × (Bool × P.experiment.Tape) =>
      indicator (f (sample.1, (sample.2.1, (truth, sample.2.2))))) := hi.comp hm
  calc
    _ = ∫⁻ sample : Source × (Bool × P.experiment.Tape),
        indicator (f (sample.1, (sample.2.1, (truth, sample.2.2))))
          ∂ρ.prod (P.binarySymmetric.experiment.conditionalLaw fairGuessLaw truth) :=
      (lintegral_prod_symm (μ := ρ)
        (ν := P.binarySymmetric.experiment.conditionalLaw fairGuessLaw truth) _ ht.aemeasurable).symm
    _ = ∫⁻ result, indicator result ∂((ρ.prod
        (P.binarySymmetric.experiment.conditionalLaw fairGuessLaw truth)).map
          (fun sample => f (sample.1, (sample.2.1, (truth, sample.2.2))))) :=
      (lintegral_map hi hm).symm
    _ = _ := by
      rw [hconditional truth]
      exact lintegral_indicator_one hA

variable {Seed : Type u} [MeasurableSpace Seed]

/-- The actual endpoint world has its original truth/tape law; only the
independent endpoint tie coin is added by the simulator. -/
noncomputable def simulatorMixedSampledStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : ((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (Bool × (Bool × P.experiment.Tape))) : Seed × EntryHistory P.sharedInstance :=
  simulatorSampledStageExit P fee hfee source stage sample.2.2.1
    (sample.1, (sample.2.1, sample.2.2.2))

set_option maxHeartbeats 800000 in
theorem measurable_simulatorMixedSampledStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (simulatorMixedSampledStageExit P fee hfee source stage) := by
  let build := fun pair : (((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (Bool × P.experiment.Tape)) × Bool => simulatorSampledStageExit P fee hfee source stage pair.2 pair.1
  have hb : Measurable build := measurable_from_prod_countable_left
    (fun truth => measurable_simulatorSampledStageExit P fee hfee source hm stage truth)
  have hp : Measurable (fun sample : ((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (Bool × (Bool × P.experiment.Tape)) =>
      ((sample.1, (sample.2.1, sample.2.2.2)), sample.2.2.1)) :=
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_snd.comp measurable_snd).comp measurable_snd))).prodMk
        ((measurable_fst.comp measurable_snd).comp measurable_snd)
  exact hb.comp hp

/-- The concrete sampled stage under the original ACTUAL world law has
exactly the original source full-stage exit law. No actual truth is fixed
or conditioned upon in this conclusion. -/
theorem simulatorMixedSampledStageExit_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage) (ν : Measure (Seed × List (VisibleEvent P.sharedInstance)))
    [IsProbabilityMeasure ν]
    (hf : ∀ truth, P.binarySymmetric.experiment.expectedSamples ν
      (simulatorLocalTest P fee hfee source hm stage) truth ≠ ⊤) :
    ((ν.prod (auxiliaryTapeLaw P)).prod (simulatorEndpointLaw P fee hfee stage)).map
      (simulatorMixedSampledStageExit P fee hfee source stage) =
      (sourceDirectStageExitLaw P fee hfee source hm stage ν).map (fun result => (result.1, some result.2)) := by
  have hρ : SFinite (ν.prod (auxiliaryTapeLaw P) :
      Measure ((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape)) := by
    change SFinite (ν.prod (auxiliaryTapeLaw P) :
      Measure ((Seed × List (VisibleEvent P.sharedInstance)) × P.binarySymmetric.experiment.Tape))
    infer_instance
  apply @prod_simulatorEndpointLaw_map_of_conditional_constant
    (((Seed × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape))
    (Seed × EntryHistory P.sharedInstance) _ _ P fee hfee stage _ hρ
    (simulatorMixedSampledStageExit P fee hfee source stage)
    (measurable_simulatorMixedSampledStageExit P fee hfee source hm stage)
  intro truth
  exact simulatorSampledStageExit_law P fee hfee source hm stage ν hf truth

end PDROC
