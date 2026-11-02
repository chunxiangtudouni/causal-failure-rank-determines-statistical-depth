module

public import PaperProofs.Paid.PDROC_EventualEntry_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory ProbabilityTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Preserve the whole fresh hidden truth/tape joint law, with the old seed
and complete eventual entry retained jointly at arbitrary seed universes. -/
theorem sourceEventualEntry_joint_stageWorld (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    ((P.input fee hfee).seededWorldLaw ν).map (fun sample =>
      (entryHistorySeedRecord (P.input fee hfee) C.val .uncapped accounting source.rule stage sample, sample.2 stage)) =
      (sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage).prod ((P.input fee hfee).stageLaw stage) := by
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
  have hind := (input.preBirthView_independent_next ν stage).comp hg measurable_id
  change IndepFun (fun sample => gate (input.preBirthView stage sample))
    (fun sample : Seed × input.World => sample.2 stage) (input.seededWorldLaw ν) at hind
  rw [← heq] at hind
  have hm := measurable_entryHistorySeedRecord input C.val .uncapped accounting source.rule source.measurable_rule stage
  have ht : Measurable (fun sample : Seed × input.World => sample.2 stage) :=
    (measurable_pi_apply stage).comp measurable_snd
  rw [hind.map_prod_eq_prod_map_map hm.aemeasurable ht.aemeasurable, input.seededWorldLaw_coordinate]
  rfl

end PDROC
