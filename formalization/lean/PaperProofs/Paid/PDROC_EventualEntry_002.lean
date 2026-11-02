module

public import PaperProofs.Paid.PDROC_EventualEntry_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem sourceEventualEntryTest_stop_some (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) (seed : Seed)
    (entry : List (VisibleEvent P.sharedInstance)) (tape : P.binarySymmetric.experiment.Tape) :
    (sourceEventualEntryTest P fee hfee source hm stage).rule.stop (seed, some entry) tape =
      headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P source) (seed, entry) tape := by
  simp only [sourceEventualEntryTest, pullbackSeedTest, simulatorLocalTest, nativeHeadTest,
    sourceEventualHistorySeed, Option.getD_some, headExitStop, simulatorPrewriteRule,
    sourceForOptionalHistory, Option.isSome_some, ↓reduceIte]

theorem sourceEventualEntryTest_stop_none (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) (stage : P.sharedInstance.Stage) (seed : Seed)
    (tape : P.binarySymmetric.experiment.Tape) :
    (sourceEventualEntryTest P fee hfee source hm stage).rule.stop (seed, none) tape = 0 := by
  change headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P (sourceForOptionalHistory source))
    ((seed, none), []) tape = 0
  apply le_antisymm
  · apply (headExitStop_le_iff (P.input fee hfee) stage _ _ _ 0).mpr
    refine ⟨0, le_rfl, ?_⟩
    simp only [simulatorPrewriteRule, sourceForOptionalHistory, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]
  · exact zero_le

/-- Eventual entry needs no sum of future bills. Its actual direct test
charge is exactly this stage's full original observation expectation. -/
theorem sourceEventualEntryTest_bayesCharge_eq_stageBill (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    P.binarySymmetric.experiment.bayesObservationCharge
      (sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage)
      (sourceEventualEntryTest P fee hfee source.rule source.measurable_rule stage) =
      ∫⁻ sample, runStageObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule stage sample
        ∂(P.input fee hfee).seededWorldLaw ν := by
  let input := P.input fee hfee
  let test := sourceEventualEntryTest P fee hfee source.rule source.measurable_rule stage
  let f := fun pair : (Seed × EntryHistory P.sharedInstance) × P.binarySymmetric.experiment.Tape =>
    P.binarySymmetric.experiment.observationCharge (test.rule.stop pair.1 pair.2)
  have hf : Measurable f :=
    (measurable_of_countable P.binarySymmetric.experiment.observationCharge).comp test.measurable_stop
  let joint : Seed × input.World → (Seed × EntryHistory P.sharedInstance) × P.binarySymmetric.experiment.Tape := fun sample =>
    (entryHistorySeedRecord input C.val .uncapped accounting source.rule stage sample,
      worldTapes input sample.2 stage)
  have hjoint : Measurable joint :=
    (measurable_entryHistorySeedRecord input C.val .uncapped accounting source.rule source.measurable_rule stage).prodMk
      ((measurable_worldTape input stage).comp measurable_snd)
  have hlaw : (input.seededWorldLaw ν).map joint =
      (sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage).prod (auxiliaryTapeLaw P) :=
    sourceEventualEntry_joint_directTape P fee hfee C accounting source ν stage
  rw [bayesObservationCharge_eq_auxiliaryTape_integral]
  change (∫⁻ pair, f pair ∂(sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage).prod
    (auxiliaryTapeLaw P)) = _
  rw [← hlaw, lintegral_map hf hjoint]
  apply lintegral_congr
  intro sample
  cases he : entryHistory input C.val .uncapped accounting source.rule stage sample with
  | none =>
    change P.binarySymmetric.experiment.observationCharge (test.rule.stop
      (sample.1, entryHistory input C.val .uncapped accounting source.rule stage sample) _) = _
    rw [he, sourceEventualEntryTest_stop_none, P.binarySymmetric.experiment.observationCharge_zero]
    exact (runStageObservationBill_zero_of_no_entry input C.val .uncapped accounting source.rule source.legal stage sample he).symm
  | some entry =>
    obtain ⟨start, hc, hb, hh⟩ := (entryHistory_some_iff input C.val .uncapped accounting source.rule stage sample entry).mp he
    have hfirst : FirstEntryAt input C.val .uncapped accounting source.rule stage.val start sample := ⟨hc, hb⟩
    change P.binarySymmetric.experiment.observationCharge (test.rule.stop
      (sample.1, entryHistory input C.val .uncapped accounting source.rule stage sample) _) = _
    rw [he, sourceEventualEntryTest_stop_some, ← hh]
    exact firstEntry_direct_observationCharge_eq_stageBill P fee hfee C accounting source.rule source.legal sample start stage hfirst

theorem sourceEventualEntryTest_bayesCharge_le_fullBill (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    P.binarySymmetric.experiment.bayesObservationCharge
      (sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage)
      (sourceEventualEntryTest P fee hfee source.rule source.measurable_rule stage) ≤
      expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν := by
  rw [sourceEventualEntryTest_bayesCharge_eq_stageBill]
  unfold expectedBill
  apply lintegral_mono
  intro sample
  have hstage : runStageObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule stage sample ≤
      runObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule sample := by
    rw [runObservationBill_eq_sum_stage (P.input fee hfee) C.val .uncapped accounting source.rule source.legal sample]
    exact Finset.single_le_sum
      (f := fun i : P.sharedInstance.Stage => runStageObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule i sample)
      (fun _ _ => zero_le) (Finset.mem_univ stage)
  exact hstage.trans (runObservationBill_le_actual (P.input fee hfee) C.val .uncapped accounting source.rule sample)

/-- The ORIGINAL finite full bill derives the eventual-entry finite ET
needed for the kernel; no entry normalization or new comparator restriction. -/
theorem sourceEventualDraw_finiteET_of_fullBill (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    ∀ truth, P.binarySymmetric.experiment.expectedSamples
      (sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage)
      (simulatorLocalTest P fee hfee (sourceForOptionalHistory source.rule)
        (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage) truth ≠ ⊤ := by
  have hc := ne_top_of_le_ne_top hfinite
    (sourceEventualEntryTest_bayesCharge_le_fullBill P fee hfee C accounting source ν stage)
  have ho : P.binarySymmetric.experiment.bayesObjective
      (sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage)
      (sourceEventualEntryTest P fee hfee source.rule source.measurable_rule stage) 0 ≠ ⊤ := by
    simpa only [BinaryExperiment.bayesObjective, zero_mul, add_zero] using hc
  have hf := P.binarySymmetric.experiment.bayesObjective_finite_expectedSamples _ _ 0 ho
  intro truth
  simpa only [sourceEventualEntryTest, expectedSamples_pullbackSeedTest, sourceEventualDrawSeedLaw] using hf truth

theorem sourceObservationBill_eq_sum_eventualCharges (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    (∑ stage : P.sharedInstance.Stage, P.binarySymmetric.experiment.bayesObservationCharge
      (sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage)
      (sourceEventualEntryTest P fee hfee source.rule source.measurable_rule stage)) =
      expectedObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule ν := by
  simp_rw [sourceEventualEntryTest_bayesCharge_eq_stageBill]
  exact (expectedObservationBill_eq_sum_stage (P.input fee hfee) C.val .uncapped accounting
    source.rule source.legal source.measurable_rule ν).symm

end PDROC
