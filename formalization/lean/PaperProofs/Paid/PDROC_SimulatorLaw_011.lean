module

public import PaperProofs.Paid.PDROC_SimulatorLaw_010
public import PaperProofs.Paid.PDROC_EventualEntry_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u v

theorem prod_stageLaw_map {I : Instance} {Source : Type u} {Target : Type v}
    [MeasurableSpace Source] [MeasurableSpace Target]
    (input : StatisticalInput I) (stage : I.Stage) (ρ : Measure Source) [SFinite ρ]
    (f : Source × input.StageSample stage → Target) (hf : Measurable f) :
    (ρ.prod (input.stageLaw stage)).map f =
      (input.experiment stage).priorMass true •
        (((input.experiment stage).conditionalLaw ρ true).map
          (fun sample => f (sample.1, (true, sample.2)))) +
      (input.experiment stage).priorMass false •
        (((input.experiment stage).conditionalLaw ρ false).map
          (fun sample => f (sample.1, (false, sample.2)))) := by
  have hfixed (truth : Bool) :
      (ρ.prod ((Measure.dirac truth).prod ((input.experiment stage).tapeLaw truth))).map f =
        ((input.experiment stage).conditionalLaw ρ truth).map
          (fun sample => f (sample.1, (truth, sample.2))) := by
    have ht : Measurable (fun tape : (input.experiment stage).Tape => (truth, tape)) :=
      measurable_const.prodMk measurable_id
    have hmap := Measure.map_prod_map ρ ((input.experiment stage).tapeLaw truth) measurable_id ht
    rw [Measure.map_id] at hmap
    rw [Measure.dirac_prod, hmap, Measure.map_map hf (measurable_id.prodMap ht)]
    rfl
  unfold StatisticalInput.stageLaw
  rw [Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.map_add _ _ hf, Measure.map_smul _ hf.aemeasurable, Measure.map_smul _ hf.aemeasurable,
    hfixed, hfixed]

variable {Seed : Type u} [MeasurableSpace Seed]

/-- The original source's complete stopped direct draw, reported with the
original actual source truth. No simulator coordinate flip occurs here. -/
noncomputable def sourceDirectReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (stage : P.sharedInstance.Stage)
    (sample : (Seed × List (VisibleEvent P.sharedInstance)) × (P.input fee hfee).StageSample stage) :
    (((Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance) × Bool) :=
  (simulatorDrawPair P fee hfee source stage
    (P.binarySymmetric.experiment.stoppedTranscript (simulatorLocalTest P fee hfee source hm stage)
      (sample.1, sample.2.2)), sample.2.1)

theorem measurable_sourceDirectReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (sourceDirectReportedDraw P fee hfee source hm stage) := by
  have hp : Measurable (fun sample : (Seed × List (VisibleEvent P.sharedInstance)) ×
      (P.input fee hfee).StageSample stage => (sample.1, sample.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have ht := (P.binarySymmetric.experiment.measurable_stoppedTranscript
    (simulatorLocalTest P fee hfee source hm stage)).comp hp
  exact ((measurable_simulatorDrawPair P fee hfee source hm stage).comp ht).prodMk
    (measurable_fst.comp measurable_snd)

theorem sourceDirectReportedDraw_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (ν : Measure (Seed × List (VisibleEvent P.sharedInstance))) [IsProbabilityMeasure ν] :
    (ν.prod ((P.input fee hfee).stageLaw stage)).map
      (sourceDirectReportedDraw P fee hfee source hm stage) =
      simulatorSourceReportedDrawLaw P fee hfee source hm stage ν := by
  have hd := measurable_simulatorDrawPair P fee hfee source hm stage
  have htag (truth : Bool) : Measurable
      (fun record : (Seed × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance => (record, truth)) :=
    measurable_id.prodMk measurable_const
  have ht := P.binarySymmetric.experiment.measurable_stoppedTranscript
    (simulatorLocalTest P fee hfee source hm stage)
  have hconditional (truth : Bool) :
      ((P.binarySymmetric.experiment.conditionalLaw ν truth).map
        (fun sample => sourceDirectReportedDraw P fee hfee source hm stage (sample.1, (truth, sample.2)))) =
      ((P.binarySymmetric.experiment.transcriptLaw ν (simulatorLocalTest P fee hfee source hm stage) truth).map
        (simulatorDrawPair P fee hfee source stage)).map (fun record => (record, truth)) := by
    unfold PaperProofs.Statistics.BinaryExperiment.transcriptLaw
    rw [Measure.map_map (htag truth) hd, Measure.map_map ((htag truth).comp hd) ht]
    rfl
  rw [prod_stageLaw_map (P.input fee hfee) stage ν _ (measurable_sourceDirectReportedDraw P fee hfee source hm stage)]
  change P.binarySymmetric.experiment.priorMass true •
      ((P.binarySymmetric.experiment.conditionalLaw ν true).map
        (fun sample => sourceDirectReportedDraw P fee hfee source hm stage (sample.1, (true, sample.2)))) +
    P.binarySymmetric.experiment.priorMass false •
      ((P.binarySymmetric.experiment.conditionalLaw ν false).map
        (fun sample => sourceDirectReportedDraw P fee hfee source hm stage (sample.1, (false, sample.2)))) = _
  rw [hconditional true, hconditional false, P.binarySymmetric.priorMass_eq_half,
    P.binarySymmetric.priorMass_eq_half]
  exact add_comm _ _

end PDROC
