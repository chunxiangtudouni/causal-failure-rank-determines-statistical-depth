module

public import PaperProofs.Paid.PDROC_LocalRecord_017
public import PaperProofs.Common.HistorySuffixWorld

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u} [MeasurableSpace Seed]

/-- Blind stop is only the no-entry analysis completion; every real
eventual entry calls the original complete-history source rule. -/
def sourceForOptionalHistory (source : PolicyRule I Seed) : PolicyRule I (Seed × EntryHistory I) :=
  fun seed history => if seed.2.isSome = true then source seed.1 history else .stop

theorem measurable_sourceForOptionalHistory (source : PolicyRule I Seed) (hm : MeasurableRule source) :
    MeasurableRule (sourceForOptionalHistory source) := by
  have hs : Measurable (fun pair : (Seed × EntryHistory I) × List (VisibleEvent I) =>
      source pair.1.1 pair.2) := hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hg : MeasurableSet {pair : (Seed × EntryHistory I) × List (VisibleEvent I) | pair.1.2.isSome = true} :=
    ((measurable_of_countable (fun history : EntryHistory I => history.isSome)).comp
      (measurable_snd.comp measurable_fst)) (measurableSet_singleton true)
  exact hs.ite hg measurable_const

def sourceEventualHistorySeed (seed : Seed × EntryHistory I) :
    (Seed × EntryHistory I) × List (VisibleEvent I) := (seed, seed.2.getD [])

theorem measurable_sourceEventualHistorySeed : Measurable (sourceEventualHistorySeed (I := I) (Seed := Seed)) :=
  measurable_id.prodMk ((measurable_of_countable (fun entry : EntryHistory I => entry.getD [])).comp measurable_snd)

noncomputable def sourceEventualEntrySeedLaw (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (ν : Measure Seed)
    (stage : P.sharedInstance.Stage) : Measure (Seed × EntryHistory P.sharedInstance) :=
  ((P.input fee hfee).seededWorldLaw ν).map
    (entryHistorySeedRecord (P.input fee hfee) C.val .uncapped accounting source.rule stage)

instance sourceEventualEntrySeedLaw_probability (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    IsProbabilityMeasure (sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) := by
  unfold sourceEventualEntrySeedLaw
  infer_instance

noncomputable def sourceEventualDrawSeedLaw (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (ν : Measure Seed)
    (stage : P.sharedInstance.Stage) :
    Measure ((Seed × EntryHistory P.sharedInstance) × List (VisibleEvent P.sharedInstance)) :=
  (sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage).map sourceEventualHistorySeed

instance sourceEventualDrawSeedLaw_probability (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    IsProbabilityMeasure (sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage) := by
  unfold sourceEventualDrawSeedLaw
  infer_instance

noncomputable def sourceEventualEntryTest (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    P.binarySymmetric.experiment.AdmissibleRule (Seed × EntryHistory P.sharedInstance) :=
  pullbackSeedTest P.binarySymmetric.experiment
    (simulatorLocalTest P fee hfee (sourceForOptionalHistory source)
      (measurable_sourceForOptionalHistory source hm) stage)
    sourceEventualHistorySeed measurable_sourceEventualHistorySeed

/-- The complete old seed and eventual history, including never-entry,
remain independent of the current real tape for arbitrary seed universes. -/
theorem sourceEventualEntry_joint_directTape (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    ((P.input fee hfee).seededWorldLaw ν).map (fun sample =>
      (entryHistorySeedRecord (P.input fee hfee) C.val .uncapped accounting source.rule stage sample,
        worldTapes (P.input fee hfee) sample.2 stage)) =
      (sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage).prod (auxiliaryTapeLaw P) := by
  let input := P.input fee hfee
  let complete : Seed × input.PastWorld stage → Seed × input.World :=
    fun sample => (sample.1, completePastWorld input stage sample.2)
  have hc : Measurable complete := measurable_fst.prodMk
    ((measurable_completePastWorld input stage).comp measurable_snd)
  let gate : Seed × input.PastWorld stage → Seed × EntryHistory P.sharedInstance :=
    fun sample => (sample.1, entryHistory input C.val .uncapped accounting source.rule stage (complete sample))
  have hg : Measurable gate := measurable_fst.prodMk
    ((measurable_entryHistory input C.val .uncapped accounting source.rule source.measurable_rule stage).comp hc)
  have heq : entryHistorySeedRecord input C.val .uncapped accounting source.rule stage =
      fun sample => gate (input.preBirthView stage sample) := by
    funext sample
    apply Prod.ext
    · rfl
    · exact (entryHistory_eq_of_past input C.val .uncapped accounting source.rule source.legal sample.1 sample.2
        (completePastWorld input stage (fun i => sample.2 i.val)) stage
        (fun i hi => completePastWorld_apply_past input stage (fun i => sample.2 i.val) i hi)).symm
  have hind := (input.preBirthView_independent_next ν stage).comp hg measurable_snd
  change IndepFun (fun sample => gate (input.preBirthView stage sample))
    (fun sample : Seed × input.World => worldTapes input sample.2 stage) (input.seededWorldLaw ν) at hind
  rw [← heq] at hind
  have hm := measurable_entryHistorySeedRecord input C.val .uncapped accounting source.rule source.measurable_rule stage
  have ht : Measurable (fun sample : Seed × input.World => worldTapes input sample.2 stage) :=
    (measurable_worldTape input stage).comp measurable_snd
  rw [hind.map_prod_eq_prod_map_map hm.aemeasurable ht.aemeasurable, seededCurrentTape_law]
  rfl

end PDROC
