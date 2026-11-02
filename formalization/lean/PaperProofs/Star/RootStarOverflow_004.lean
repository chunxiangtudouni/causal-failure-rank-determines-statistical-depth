module

public import PaperProofs.Common.NativeTestingKernel
public import PaperProofs.Star.PStarLR_RealThreshold_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace RootStarOverflow

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

universe u

noncomputable def entryRecord {I : Instance} {Seed : Type u} (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (stage : I.Stage) (sample : Seed × input.World) : Seed × EntryHistory I :=
  (sample.1, entryHistory input C mode accounting rule stage sample)

theorem measurable_entryRecord {I : Instance} {Seed : Type u} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hm : MeasurableRule rule) (stage : I.Stage) :
    Measurable (entryRecord input C mode accounting rule stage) :=
  measurable_fst.prodMk (measurable_entryHistory input C mode accounting rule hm stage)

theorem entryRecord_independent_stage {I : Instance} {Seed : Type u} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (nu : Measure Seed) [IsProbabilityMeasure nu]
    (stage : I.Stage) :
    IndepFun (entryRecord input C mode accounting policy.rule stage)
      (fun sample : Seed × input.World => sample.2 stage) (input.seededWorldLaw nu) := by
  let complete : Seed × input.PastWorld stage → Seed × input.World :=
    fun sample => (sample.1, completePastWorld input stage sample.2)
  have hc : Measurable complete :=
    measurable_fst.prodMk ((measurable_completePastWorld input stage).comp measurable_snd)
  let joint : Seed × input.PastWorld stage → Seed × EntryHistory I :=
    fun sample => (sample.1, entryHistory input C mode accounting policy.rule stage (complete sample))
  have hj : Measurable joint := measurable_fst.prodMk
    ((measurable_entryHistory input C mode accounting policy.rule policy.measurable_rule stage).comp hc)
  have heq : entryRecord input C mode accounting policy.rule stage =
      fun sample => joint (input.preBirthView stage sample) := by
    funext sample
    apply Prod.ext
    · rfl
    exact (entryHistory_eq_of_past input C mode accounting policy.rule policy.legal sample.1 sample.2
      (completePastWorld input stage (fun i => sample.2 i.val)) stage
      (fun i hi => completePastWorld_apply_past input stage (fun i => sample.2 i.val) i hi)).symm
  rw [heq]
  exact input.preBirthRecord_independent_next nu stage joint hj

theorem entryRecord_jointLaw {I : Instance} {Seed : Type u} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (nu : Measure Seed) [IsProbabilityMeasure nu]
    (stage : I.Stage) :
    (input.seededWorldLaw nu).map (fun sample =>
        (entryRecord input C mode accounting policy.rule stage sample, sample.2 stage)) =
      ((input.seededWorldLaw nu).map (entryRecord input C mode accounting policy.rule stage)).prod
        (input.stageLaw stage) := by
  have hind := entryRecord_independent_stage input C mode accounting policy nu stage
  have hs : Measurable (fun sample : Seed × input.World => sample.2 stage) :=
    (measurable_pi_apply stage).comp measurable_snd
  rw [hind.map_prod_eq_prod_map_map
    (measurable_entryRecord input C mode accounting policy.rule policy.measurable_rule stage).aemeasurable
    hs.aemeasurable, input.seededWorldLaw_coordinate]

end RootStarOverflow
