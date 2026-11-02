module

public import PaperProofs.Paid.PDROC_OverlayKernel_008
public import PaperProofs.Paid.PDROC_OverlayEntry_007
public import PaperProofs.Paid.PDROC_SimulatorLaw_014

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

noncomputable def overlaySeedLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) : Measure (OverlaySeed P Seed) :=
  overlayFreshSeedLaw P ν (overlayPaidStageCoinsLaw P fee hfee)

instance overlaySeedLaw_probability (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) [IsProbabilityMeasure ν] : IsProbabilityMeasure (overlaySeedLaw P fee hfee ν) := by
  unfold overlaySeedLaw
  infer_instance

def overlayProofCoinRow : OverlayStageCoins := (fun _ => (false, false), fun _ => false)

noncomputable def overlayEventualStageSample (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) :
    ((((Seed × EntryHistory P.sharedInstance) × List (VisibleEvent P.sharedInstance)) × P.experiment.Tape) ×
      (OverlayStageCoins × (Bool × P.experiment.Tape))) :=
  ((sourceEventualHistorySeed (overlayVirtualEntryGate P fee hfee C accounting source stage sample),
    sample.1.2.1 stage), (sample.1.2.2 stage, sample.2 stage))

theorem measurable_overlayEventualStageSample (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (overlayEventualStageSample P fee hfee C accounting source stage) := by
  have hg : Measurable (overlayVirtualEntryGate P fee hfee C accounting source stage) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_overlayVirtualEntry P fee hfee C accounting source hm stage)
  exact ((measurable_sourceEventualHistorySeed.comp hg).prodMk
    ((measurable_pi_apply stage).comp ((measurable_fst.comp measurable_snd).comp measurable_fst))).prodMk
      (((measurable_pi_apply stage).comp ((measurable_snd.comp measurable_snd).comp measurable_fst)).prodMk
        ((measurable_pi_apply stage).comp measurable_snd))

noncomputable def overlayEventualStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) :
    (Seed × EntryHistory P.sharedInstance) × EntryHistory P.sharedInstance :=
  overlayMixedSampledStageExit P fee hfee (sourceForOptionalHistory source) stage
    (overlayEventualStageSample P fee hfee C accounting source stage sample)

theorem measurable_overlayEventualStageExit (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) :
    Measurable (overlayEventualStageExit P fee hfee C accounting source stage) :=
  (measurable_overlayMixedSampledStageExit P fee hfee (sourceForOptionalHistory source)
    (measurable_sourceForOptionalHistory source hm) stage).comp
      (measurable_overlayEventualStageSample P fee hfee C accounting source hm stage)

set_option maxHeartbeats 800000 in
/-- Only current entry-law equality remains as the induction hypothesis.
Freshness is proved for the actual guarded rule, including current aux tape. -/
theorem overlayEventualStageSample_law_of_entryLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hentry : ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
      (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage) :
    ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
      (overlayEventualStageSample P fee hfee C accounting source.rule stage) =
      ((sourceEventualDrawSeedLaw P 0 (by norm_num) C accounting source ν stage).prod (auxiliaryTapeLaw P)).prod
        ((overlayPaidStageCoinsLaw P fee hfee).prod ((P.input fee hfee).stageLaw stage)) := by
  let entryLaw := sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage
  let rowLaw := overlayPaidStageCoinsLaw P fee hfee
  let worldLaw : Measure (Bool × P.experiment.Tape) := (P.input fee hfee).stageLaw stage
  let : IsProbabilityMeasure worldLaw := by
    dsimp only [worldLaw]
    change IsProbabilityMeasure ((P.input fee hfee).stageLaw stage)
    infer_instance
  let augment := sourceEventualHistorySeed (I := P.sharedInstance) (Seed := Seed)
  let build := fun pair : (Seed × EntryHistory P.sharedInstance) ×
      ((P.experiment.Tape × OverlayStageCoins) × (Bool × P.experiment.Tape)) =>
    ((augment pair.1, pair.2.1.1), (pair.2.1.2, pair.2.2))
  have ha : Measurable augment := measurable_sourceEventualHistorySeed
  have hb : Measurable build :=
    ((ha.comp measurable_fst).prodMk ((measurable_fst.comp measurable_fst).comp measurable_snd)).prodMk
      (((measurable_snd.comp measurable_fst).comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
  have h0 := (MeasurePreserving.id entryLaw).prod
    (measurePreserving_prodAssoc (auxiliaryTapeLaw P) rowLaw worldLaw)
  have h1 := (measurePreserving_prodAssoc entryLaw (auxiliaryTapeLaw P) (rowLaw.prod worldLaw)).symm
    MeasurableEquiv.prodAssoc
  have hAug : MeasurePreserving augment entryLaw (sourceEventualDrawSeedLaw P 0 (by norm_num) C accounting source ν stage) :=
    ⟨ha, rfl⟩
  have h2 := (hAug.prod (MeasurePreserving.id (auxiliaryTapeLaw P))).prod
    (MeasurePreserving.id (rowLaw.prod worldLaw))
  have hbuild : (entryLaw.prod (((auxiliaryTapeLaw P).prod rowLaw).prod worldLaw)).map build =
      ((sourceEventualDrawSeedLaw P 0 (by norm_num) C accounting source ν stage).prod (auxiliaryTapeLaw P)).prod
        (rowLaw.prod worldLaw) := ((h2.comp h1).comp h0).map_eq
  have hj := overlayVirtualEntry_joint_actualMarginal P fee hfee C accounting source.rule source.measurable_rule
    ν rowLaw stage overlayProofCoinRow
  change ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
    (fun sample => (overlayVirtualEntryGate P fee hfee C accounting source.rule stage sample,
      overlayFullCurrent P fee hfee stage sample)) =
      (((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
        (overlayVirtualEntryGate P fee hfee C accounting source.rule stage)).prod
          (((auxiliaryTapeLaw P).prod rowLaw).prod worldLaw) at hj
  rw [hentry] at hj
  have hg : Measurable (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_overlayVirtualEntry P fee hfee C accounting source.rule source.measurable_rule stage)
  have hn : Measurable (overlayFullCurrent (Seed := Seed) (Row := OverlayStageCoins) P fee hfee stage) := by
    unfold overlayFullCurrent
    fun_prop
  calc
    _ = (((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
        (fun sample => (overlayVirtualEntryGate P fee hfee C accounting source.rule stage sample,
          overlayFullCurrent P fee hfee stage sample))).map build :=
      (Measure.map_map hb (hg.prodMk hn)).symm
    _ = _ := by rw [hj]; exact hbuild

/-- The source's finite complete free bill derives the local ETs. No extra
ET premise is added: only the current entry law remains for stage induction. -/
theorem overlayEventualStageExit_law_of_entryLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
      (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage) :
    ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
      (overlayEventualStageExit P fee hfee C accounting source.rule stage) =
      ((P.input 0 (by norm_num)).seededWorldLaw ν).map
        (sourceEventualStageExitSome P 0 (by norm_num) C accounting source stage) := by
  have hm := measurable_overlayMixedSampledStageExit P fee hfee (sourceForOptionalHistory source.rule)
    (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage
  calc
    _ = (((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
        (overlayEventualStageSample P fee hfee C accounting source.rule stage)).map
          (overlayMixedSampledStageExit P fee hfee (sourceForOptionalHistory source.rule) stage) :=
      (Measure.map_map hm (measurable_overlayEventualStageSample P fee hfee C accounting source.rule source.measurable_rule stage)).symm
    _ = (sourceDirectStageExitLaw P 0 (by norm_num) (sourceForOptionalHistory source.rule)
        (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage
          (sourceEventualDrawSeedLaw P 0 (by norm_num) C accounting source ν stage)).map
            (fun result => (result.1, some result.2)) := by
      rw [overlayEventualStageSample_law_of_entryLaw P fee hfee C accounting source ν stage hentry]
      exact overlayMixedSampledStageExit_law P fee hfee (sourceForOptionalHistory source.rule)
        (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage _
          (sourceEventualDraw_finiteET_of_fullBill P 0 (by norm_num) C accounting source ν stage hfinite)
    _ = _ := (sourceEventualStageExitSome_law P 0 (by norm_num) C accounting source ν stage).symm

end PDROC
