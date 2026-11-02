module
public import PaperProofs.Paid.PDROC_LocalRecord_005

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid
open PaperProofs.Statistics

namespace PDROC
universe u v

/-- Pull back a genuine admissible test along a measurable independent-seed
map. The map never receives a tape or truth argument. -/
def pullbackSeedTest (E : BinaryExperiment) {SeedA : Type u} {SeedB : Type v}
    [MeasurableSpace SeedA] [MeasurableSpace SeedB]
    (test : E.AdmissibleRule SeedB) (f : SeedA → SeedB) (hf : Measurable f) : E.AdmissibleRule SeedA where
  rule := {
    stop := fun seed tape => test.rule.stop (f seed) tape
    decision := fun seed tape => test.rule.decision (f seed) tape
    stopping := fun seed tape tape' n hp => test.rule.stopping (f seed) tape tape' n hp
    stoppedDecision := fun seed tape tape' n hs hs' hp => test.rule.stoppedDecision (f seed) tape tape' n hs hs' hp
  }
  measurable_stop := test.measurable_stop.comp ((hf.comp measurable_fst).prodMk measurable_snd)
  measurable_decision := test.measurable_decision.comp ((hf.comp measurable_fst).prodMk measurable_snd)

theorem bayesObservationCharge_eq_auxiliaryTape_integral (P : Parameters)
    {Source : Type u} [MeasurableSpace Source] (ν : Measure Source) [SFinite ν]
    (test : P.binarySymmetric.experiment.AdmissibleRule Source) :
    P.binarySymmetric.experiment.bayesObservationCharge ν test =
      ∫⁻ sample, P.binarySymmetric.experiment.observationCharge (test.rule.stop sample.1 sample.2)
        ∂ν.prod (auxiliaryTapeLaw P) := by
  rw [prod_auxiliaryTapeLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  unfold BinaryExperiment.bayesObservationCharge BinaryExperiment.expectedObservationCharge
  rw [Fintype.sum_bool, P.binarySymmetric.priorMass_eq_half, P.binarySymmetric.priorMass_eq_half]
  simp only [smul_eq_mul]
  exact add_comm _ _

section
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Blind completion outside the genuine fixed-clock first-entry event.
The default public cache contains no unobserved truth or tape and is never
queried by the test on the none branch. -/
noncomputable def optionalSourceEntryTest (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) :
    P.binarySymmetric.experiment.AdmissibleRule (Seed × Option (Startup P.sharedInstance)) :=
  P.binarySymmetric.preBirthTest
    (pullbackSeedTest P.binarySymmetric.experiment (sourceEntryTest P fee hfee first accounting rule hm)
      (fun seed => (seed.1, seed.2.getD (publicStartup (initial (fun _ => false)))))
      (measurable_fst.prodMk ((measurable_of_countable
        (fun startup : Option (Startup P.sharedInstance) => startup.getD (publicStartup (initial (fun _ => false))))).comp measurable_snd)))
    {seed | seed.2.isSome = true}
    (((measurable_of_countable (fun startup : Option (Startup P.sharedInstance) => startup.isSome)).comp
      measurable_snd) (measurableSet_singleton true))

theorem optionalSourceEntryTest_stop_some (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule)
    (seed : Seed) (startup : Startup P.sharedInstance) (tape : P.binarySymmetric.experiment.Tape) :
    (optionalSourceEntryTest P fee hfee first accounting rule hm).rule.stop (seed, some startup) tape =
      (sourceEntryTest P fee hfee first accounting rule hm).rule.stop (seed, startup) tape := by
  simp [optionalSourceEntryTest, PaperProofs.Statistics.BinarySymmetric.Parameters.preBirthTest,
    pullbackSeedTest]

theorem optionalSourceEntryTest_stop_none (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (first : P.sharedInstance.Stage) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule)
    (seed : Seed) (tape : P.binarySymmetric.experiment.Tape) :
    (optionalSourceEntryTest P fee hfee first accounting rule hm).rule.stop (seed, none) tape = 0 := by
  simp [optionalSourceEntryTest, PaperProofs.Statistics.BinarySymmetric.Parameters.preBirthTest]

/-- The law used below is the ACTUAL original seed/full first-entry snapshot
law, including its none branch; it is never a supplied conditional law. -/
noncomputable def sourceEntrySeedLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val mode accounting Seed)
    (ν : Measure Seed) (first : P.sharedInstance.Stage) (start : ℕ) :
    Measure (Seed × Option (Startup P.sharedInstance)) :=
  ((P.input fee hfee).seededWorldLaw ν).map
    (entrySeedStartupAt (P.input fee hfee) C.val mode accounting source.rule first start)

instance sourceEntrySeedLaw_probability (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (first : P.sharedInstance.Stage) (start : ℕ) :
    IsProbabilityMeasure (sourceEntrySeedLaw P fee hfee C mode accounting source ν first start) := by
  unfold sourceEntrySeedLaw
  infer_instance

/-- The entire actual local source-test cost is paid by the original FULL
actual bill, with all failed executions still included. No finite-cost or
finite-ET hypothesis is used in this inequality. -/
theorem optionalSourceEntryTest_bayesCharge_le_fullBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (first : P.sharedInstance.Stage) (start : ℕ) :
    P.binarySymmetric.experiment.bayesObservationCharge
      (sourceEntrySeedLaw P fee hfee C mode accounting source ν first start)
      (optionalSourceEntryTest P fee hfee first accounting source.rule source.measurable_rule) ≤
      expectedBill (P.input fee hfee) C.val mode accounting source.rule ν := by
  let input := P.input fee hfee
  let test := optionalSourceEntryTest P fee hfee first accounting source.rule source.measurable_rule
  let f := fun pair : (Seed × Option (Startup P.sharedInstance)) × P.binarySymmetric.experiment.Tape =>
    P.binarySymmetric.experiment.observationCharge (test.rule.stop pair.1 pair.2)
  have hf : Measurable f := (measurable_of_countable P.binarySymmetric.experiment.observationCharge).comp test.measurable_stop
  let joint := fun sample : Seed × input.World =>
    (entrySeedStartupAt input C.val mode accounting source.rule first start sample,
      sourceEntryTape P fee hfee first (input.restrictFreshWorld first.val sample.2))
  have hjoint : Measurable joint :=
    (measurable_entrySeedStartupAt input C.val mode accounting source.rule source.measurable_rule first start).prodMk
      ((measurable_sourceEntryTape P fee hfee first).comp
        ((input.measurable_restrictFreshWorld first.val).comp measurable_snd))
  have hlaw := sourceEntry_joint_auxiliaryTape P fee hfee C mode accounting source ν first start
  rw [bayesObservationCharge_eq_auxiliaryTape_integral]
  change (∫⁻ pair, f pair ∂((input.seededWorldLaw ν).map
      (entrySeedStartupAt input C.val mode accounting source.rule first start)).prod (auxiliaryTapeLaw P)) ≤ _
  rw [← hlaw, lintegral_map hf hjoint]
  unfold expectedBill
  apply lintegral_mono
  intro sample
  cases hs : entryStartupAt input C.val mode accounting source.rule first start sample with
  | none =>
    change P.binarySymmetric.experiment.observationCharge
      (test.rule.stop (sample.1, entryStartupAt input C.val mode accounting source.rule first start sample) _) ≤ _
    rw [hs, optionalSourceEntryTest_stop_none, P.binarySymmetric.experiment.observationCharge_zero]
    exact zero_le
  | some startup =>
    obtain ⟨hentry, hstartup⟩ := (entryStartupAt_some_iff input C.val mode accounting source.rule first start sample startup).mp hs
    change P.binarySymmetric.experiment.observationCharge
      (test.rule.stop (sample.1, entryStartupAt input C.val mode accounting source.rule first start sample) _) ≤ _
    rw [hs, optionalSourceEntryTest_stop_some, ← hstartup]
    exact (sourceEntryTest_observationCharge_le_future P fee hfee C mode accounting source sample first start hentry).trans
      ((futureObservationBill_le_full input C.val mode accounting source.rule start sample).trans
        (runObservationBill_le_actual input C.val mode accounting source.rule sample))

/-- Original finite FULL actual bill proves both conditional local ETs
finite. This is a derived bridge for all source comparators, never a new
qualification on the original Policy or its private-seed universe. -/
theorem optionalSourceEntryTest_finiteET_of_fullBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (first : P.sharedInstance.Stage) (start : ℕ)
    (hfinite : expectedBill (P.input fee hfee) C.val mode accounting source.rule ν ≠ ⊤) :
    ∀ truth, P.binarySymmetric.experiment.expectedSamples
      (sourceEntrySeedLaw P fee hfee C mode accounting source ν first start)
      (optionalSourceEntryTest P fee hfee first accounting source.rule source.measurable_rule) truth ≠ ⊤ := by
  have hc := ne_top_of_le_ne_top hfinite
    (optionalSourceEntryTest_bayesCharge_le_fullBill P fee hfee C mode accounting source ν first start)
  have ho : P.binarySymmetric.experiment.bayesObjective
      (sourceEntrySeedLaw P fee hfee C mode accounting source ν first start)
      (optionalSourceEntryTest P fee hfee first accounting source.rule source.measurable_rule) 0 ≠ ⊤ := by
    simpa only [BinaryExperiment.bayesObjective, zero_mul, add_zero] using hc
  exact P.binarySymmetric.experiment.bayesObjective_finite_expectedSamples _ _ 0 ho

end
end PDROC
