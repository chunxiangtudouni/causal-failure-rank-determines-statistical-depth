module
public import PaperProofs.Paid.PDROC_LocalRecord_004
public import PaperProofs.Common.HistorySuffixWorld

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid

namespace PDROC
universe u

noncomputable def experimentTapeMixture (E : PaperProofs.Statistics.BinaryExperiment) : Measure E.Tape :=
  E.priorMass true • E.tapeLaw true + E.priorMass false • E.tapeLaw false

def castExperimentTape {E F : PaperProofs.Statistics.BinaryExperiment} (h : E = F) (tape : E.Tape) : F.Tape := h ▸ tape

theorem measurable_castExperimentTape {E F : PaperProofs.Statistics.BinaryExperiment} (h : E = F) :
    Measurable (castExperimentTape h) := by
  cases h
  exact measurable_id

theorem experimentTapeMixture_cast {E F : PaperProofs.Statistics.BinaryExperiment} (h : E = F) :
    (experimentTapeMixture E).map (castExperimentTape h) = experimentTapeMixture F := by
  cases h
  exact Measure.map_id

theorem measurable_worldTape {I : Instance} (input : StatisticalInput I) (stage : I.Stage) :
    Measurable (fun world => worldTapes input world stage) :=
  (measurable_pi_apply stage).snd

theorem worldTape_map {I : Instance} (input : StatisticalInput I) (stage : I.Stage) :
    input.worldLaw.map (fun world => worldTapes input world stage) =
      experimentTapeMixture (input.experiment stage) := by
  change input.worldLaw.map (Prod.snd ∘ (fun world => world stage)) = _
  rw [← Measure.map_map measurable_snd (measurable_pi_apply stage), input.worldLaw_coordinate]
  unfold StatisticalInput.stageLaw experimentTapeMixture
  rw [Measure.map_add _ _ measurable_snd, Measure.map_smul _ measurable_snd.aemeasurable,
    Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_snd_prod, Measure.map_snd_prod]
  simp only [measure_univ, one_smul]

theorem measurable_sourceEntryTape (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) : Measurable (sourceEntryTape P fee hfee first) :=
  (measurable_castExperimentTape (sourceEntryExperiment_eq P fee hfee first)).comp
    (measurable_worldTape ((P.input fee hfee).freshSuffix first.val) (P.sharedInstance.freshHead first))

/-- The REAL fresh suffix's current tape has exactly the pure auxiliary
mixture law. This is a world-law theorem, with no latent-truth sampling API. -/
theorem sourceEntryTape_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) :
    ((P.input fee hfee).freshSuffix first.val).worldLaw.map (sourceEntryTape P fee hfee first) = auxiliaryTapeLaw P := by
  let h := sourceEntryExperiment_eq P fee hfee first
  change (((P.input fee hfee).freshSuffix first.val).worldLaw.map
    (castExperimentTape h ∘ (fun world => worldTapes ((P.input fee hfee).freshSuffix first.val) world
      (P.sharedInstance.freshHead first)))) = _
  rw [← Measure.map_map (measurable_castExperimentTape h)
    (measurable_worldTape _ _), worldTape_map, experimentTapeMixture_cast h]
  unfold experimentTapeMixture auxiliaryTapeLaw
  rw [P.binarySymmetric.priorMass_eq_half, P.binarySymmetric.priorMass_eq_half]
  exact add_comm _ _

section
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Original seed and complete genuine first-entry public cache are jointly
independent of the current fresh tape. None retains every path that does not
first enter at this clock. There is no success conditioning or normalization. -/
theorem sourceEntry_joint_auxiliaryTape (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (first : P.sharedInstance.Stage) (start : ℕ) :
    ((P.input fee hfee).seededWorldLaw ν).map (fun sample =>
      (entrySeedStartupAt (P.input fee hfee) C.val mode accounting source.rule first start sample,
        sourceEntryTape P fee hfee first ((P.input fee hfee).restrictFreshWorld first.val sample.2))) =
      (((P.input fee hfee).seededWorldLaw ν).map
        (entrySeedStartupAt (P.input fee hfee) C.val mode accounting source.rule first start)).prod
          (auxiliaryTapeLaw P) := by
  let input := P.input fee hfee
  let entry := entrySeedStartupAt input C.val mode accounting source.rule first start
  let fresh := fun sample : Seed × input.World => input.restrictFreshWorld first.val sample.2
  let f := Prod.map (id : Seed × Option (Startup P.sharedInstance) → Seed × Option (Startup P.sharedInstance))
    (sourceEntryTape P fee hfee first)
  have hmEntry := measurable_entrySeedStartupAt input C.val mode accounting source.rule source.measurable_rule first start
  have hmFresh : Measurable fresh := (input.measurable_restrictFreshWorld first.val).comp measurable_snd
  have hmF : Measurable f := measurable_id.prodMap (measurable_sourceEntryTape P fee hfee first)
  have h := congrArg (fun μ => μ.map f)
    (entrySeedStartupAt_jointFreshSuffixLaw input C.val mode accounting source ν first start)
  rw [Measure.map_map hmF (hmEntry.prodMk hmFresh),
    ← Measure.map_prod_map _ _ measurable_id (measurable_sourceEntryTape P fee hfee first),
    Measure.map_id, sourceEntryTape_law] at h
  exact h

end
end PDROC
