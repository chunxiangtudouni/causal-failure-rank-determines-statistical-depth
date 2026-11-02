module

public import PaperProofs.Paid.PDROC_SimulatorLaw_011

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u v
variable {I : Instance} {Seed : Type u}

theorem postwriteStageTrace_congr_seed_rule {OtherSeed : Type v}
    (source : PolicyRule I Seed) (other : PolicyRule I OtherSeed)
    (seed : Seed) (otherSeed : OtherSeed)
    (heq : ∀ history, source seed history = other otherSeed history)
    (stage : I.Stage) (history : List (VisibleEvent I)) (k : ℕ) :
    postwriteStageTrace source seed stage history k = postwriteStageTrace other otherSeed stage history k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [postwriteStageTrace, ih, postwriteStageStep, heq]

theorem sourcePostwriteGuardGood_congr_seed_rule {OtherSeed : Type v}
    (source : PolicyRule I Seed) (other : PolicyRule I OtherSeed)
    (seed : Seed) (otherSeed : OtherSeed)
    (heq : ∀ history, source seed history = other otherSeed history)
    (stage : I.Stage) (history : List (VisibleEvent I)) :
    sourcePostwriteGuardGood source seed stage history ↔ sourcePostwriteGuardGood other otherSeed stage history := by
  simp only [sourcePostwriteGuardGood, postwriteStageTrace_congr_seed_rule source other seed otherSeed heq, heq]

theorem simulatorDrawAt_optionalHistory_some (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (seed : Seed) (history entry : List (VisibleEvent P.sharedInstance)) (tape : P.experiment.Tape) :
    simulatorDrawAt P fee hfee (sourceForOptionalHistory source) stage (seed, some history) entry tape =
      simulatorDrawAt P fee hfee source stage seed entry tape := by
  simp only [simulatorDrawAt, headExitStop, simulatorPrewriteRule, sourceForOptionalHistory,
    Option.isSome_some, ↓reduceIte]
  rfl

theorem sourceDrawGuardGood_optionalHistory_some (source : PolicyRule I Seed) (stage : I.Stage)
    (seed : Seed) (history entry : List (VisibleEvent I)) (draw : SimulatorDraw I) (truth : Bool) :
    sourceDrawGuardGood (sourceForOptionalHistory source) stage ((((seed, some history), entry), draw), truth) ↔
      sourceDrawGuardGood source stage (((seed, entry), draw), truth) := by
  apply and_congr_right
  intro _
  exact sourcePostwriteGuardGood_congr_seed_rule (sourceForOptionalHistory source) source
    (seed, some history) seed (fun _ => rfl) stage _

theorem ae_prod_stageLaw_of_conditional {Source : Type v} [MeasurableSpace Source]
    (input : StatisticalInput I) (stage : I.Stage) (ρ : Measure Source) [SFinite ρ]
    (p : Source × input.StageSample stage → Prop) (hp : MeasurableSet {sample | p sample})
    (hconditional : ∀ truth, ∀ᵐ sample ∂(input.experiment stage).conditionalLaw ρ truth,
      p (sample.1, (truth, sample.2))) :
    ∀ᵐ sample ∂ρ.prod (input.stageLaw stage), p sample := by
  have hlaw := prod_stageLaw_map input stage ρ (id : Source × input.StageSample stage → _) measurable_id
  rw [Measure.map_id] at hlaw
  rw [hlaw, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_map_iff (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)).aemeasurable hp).mpr
      (hconditional true)
  · apply Measure.ae_smul_measure
    exact (ae_map_iff (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)).aemeasurable hp).mpr
      (hconditional false)

variable [MeasurableSpace Seed]

noncomputable def sourceEventualStageSample (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage)
    (sample : Seed × (P.input fee hfee).World) :
    (((Seed × EntryHistory P.sharedInstance) × List (VisibleEvent P.sharedInstance)) ×
      (P.input fee hfee).StageSample stage) :=
  (sourceEventualHistorySeed (entryHistorySeedRecord (P.input fee hfee) C.val .uncapped accounting source.rule stage sample),
    sample.2 stage)

theorem measurable_sourceEventualStageSample (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage) :
    Measurable (sourceEventualStageSample P fee hfee C accounting source stage) :=
  (measurable_sourceEventualHistorySeed.comp (measurable_entryHistorySeedRecord
    (P.input fee hfee) C.val .uncapped accounting source.rule source.measurable_rule stage)).prodMk
      ((measurable_pi_apply stage).comp measurable_snd)

theorem sourceEventualStageSample_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    ((P.input fee hfee).seededWorldLaw ν).map (sourceEventualStageSample P fee hfee C accounting source stage) =
      (sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage).prod ((P.input fee hfee).stageLaw stage) := by
  have hj : Measurable (fun sample : Seed × (P.input fee hfee).World =>
      (entryHistorySeedRecord (P.input fee hfee) C.val .uncapped accounting source.rule stage sample, sample.2 stage)) :=
    (measurable_entryHistorySeedRecord (P.input fee hfee) C.val .uncapped accounting source.rule source.measurable_rule stage).prodMk
      ((measurable_pi_apply stage).comp measurable_snd)
  have hm := measurable_sourceEventualHistorySeed (I := P.sharedInstance) (Seed := Seed)
  have hmap := Measure.map_prod_map (sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage)
    ((P.input fee hfee).stageLaw stage) hm measurable_id
  rw [Measure.map_id] at hmap
  calc
    _ = (((P.input fee hfee).seededWorldLaw ν).map (fun sample =>
        (entryHistorySeedRecord (P.input fee hfee) C.val .uncapped accounting source.rule stage sample, sample.2 stage))).map
          (Prod.map sourceEventualHistorySeed id) := (Measure.map_map (hm.prodMap measurable_id) hj).symm
    _ = ((sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage).prod
        ((P.input fee hfee).stageLaw stage)).map (Prod.map sourceEventualHistorySeed id) := by
      rw [sourceEventualEntry_joint_stageWorld]
    _ = _ := hmap.symm

noncomputable def sourceEventualReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage)
    (sample : Seed × (P.input fee hfee).World) :=
  sourceDirectReportedDraw P fee hfee (sourceForOptionalHistory source.rule)
    (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage
      (sourceEventualStageSample P fee hfee C accounting source stage sample)

theorem measurable_sourceEventualReportedDraw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage) :
    Measurable (sourceEventualReportedDraw P fee hfee C accounting source stage) :=
  (measurable_sourceDirectReportedDraw P fee hfee (sourceForOptionalHistory source.rule)
    (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage).comp
      (measurable_sourceEventualStageSample P fee hfee C accounting source stage)

theorem sourceEventualReportedDraw_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    ((P.input fee hfee).seededWorldLaw ν).map (sourceEventualReportedDraw P fee hfee C accounting source stage) =
      simulatorSourceReportedDrawLaw P fee hfee (sourceForOptionalHistory source.rule)
        (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage
          (sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage) := by
  have hm := measurable_sourceDirectReportedDraw P fee hfee (sourceForOptionalHistory source.rule)
    (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage
  calc
    _ = (((P.input fee hfee).seededWorldLaw ν).map
        (sourceEventualStageSample P fee hfee C accounting source stage)).map
          (sourceDirectReportedDraw P fee hfee (sourceForOptionalHistory source.rule)
            (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage) :=
      (Measure.map_map hm (measurable_sourceEventualStageSample P fee hfee C accounting source stage)).symm
    _ = _ := by rw [sourceEventualStageSample_law, sourceDirectReportedDraw_law]

end PDROC
