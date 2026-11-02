module
public import PaperProofs.Paid.PDROC_LocalRecord_015

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid
open PaperProofs.Statistics

namespace PDROC
universe u
section
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The direct simulator's source kernel has exactly the actual ORIGINAL
stage bill on its genuine first-entry atom, including stop/abandon/infinity. -/
theorem directOptionalEntryTest_bayesCharge_eq_entryStageBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) (start : ℕ) :
    P.binarySymmetric.experiment.bayesObservationCharge
      (sourceEntrySeedLaw P fee hfee C .uncapped accounting source ν stage start)
      (directOptionalEntryTest P fee hfee source.rule source.measurable_rule stage) =
      ∫⁻ sample, {sample | FirstEntryAt (P.input fee hfee) C.val .uncapped accounting source.rule stage.val start sample}.indicator
        (runStageObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule stage) sample
          ∂(P.input fee hfee).seededWorldLaw ν := by
  classical
  let input := P.input fee hfee
  let test := directOptionalEntryTest P fee hfee source.rule source.measurable_rule stage
  let f := fun pair : (Seed × Option (Startup P.sharedInstance)) × P.binarySymmetric.experiment.Tape =>
    P.binarySymmetric.experiment.observationCharge (test.rule.stop pair.1 pair.2)
  have hf : Measurable f := (measurable_of_countable P.binarySymmetric.experiment.observationCharge).comp test.measurable_stop
  let joint : Seed × input.World → (Seed × Option (Startup P.sharedInstance)) × P.binarySymmetric.experiment.Tape :=
    fun sample =>
    (entrySeedStartupAt input C.val .uncapped accounting source.rule stage start sample, worldTapes input sample.2 stage)
  have hjoint : Measurable joint :=
    (measurable_entrySeedStartupAt input C.val .uncapped accounting source.rule source.measurable_rule stage start).prodMk
      ((measurable_worldTape input stage).comp measurable_snd)
  have hlaw : (input.seededWorldLaw ν).map joint =
      (sourceEntrySeedLaw P fee hfee C .uncapped accounting source ν stage start).prod (auxiliaryTapeLaw P) :=
    sourceEntry_joint_directTape P fee hfee C .uncapped accounting source ν stage start
  rw [bayesObservationCharge_eq_auxiliaryTape_integral]
  change (∫⁻ pair, f pair ∂(sourceEntrySeedLaw P fee hfee C .uncapped accounting source ν stage start).prod (auxiliaryTapeLaw P)) = _
  rw [← hlaw, lintegral_map hf hjoint]
  apply lintegral_congr
  intro sample
  by_cases he : FirstEntryAt input C.val .uncapped accounting source.rule stage.val start sample
  · have hentry : entryStartupAt input C.val .uncapped accounting source.rule stage start sample =
        some (publicStartup (run input C.val .uncapped accounting source.rule sample start)) := by
      simp only [entryStartupAt, he, ↓reduceIte]
    change P.binarySymmetric.experiment.observationCharge
      (test.rule.stop (sample.1, entryStartupAt input C.val .uncapped accounting source.rule stage start sample) _) = _
    rw [hentry, directOptionalEntryTest_stop_some]
    change ((P.input fee hfee).experiment stage).observationCharge
      (headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P source.rule)
        (sample.1, (run (P.input fee hfee) C.val .uncapped accounting source.rule sample start).history)
        (worldTapes (P.input fee hfee) sample.2 stage)) = _
    rw [firstEntry_direct_observationCharge_eq_stageBill P fee hfee C accounting source.rule source.legal sample start stage he]
    change FirstEntryAt (P.input fee hfee) C.val .uncapped accounting source.rule stage.val start sample at he
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left he]
  · have hentry : entryStartupAt input C.val .uncapped accounting source.rule stage start sample = none := by
      simp only [entryStartupAt, he, ↓reduceIte]
    change P.binarySymmetric.experiment.observationCharge
      (test.rule.stop (sample.1, entryStartupAt input C.val .uncapped accounting source.rule stage start sample) _) = _
    rw [hentry, directOptionalEntryTest_stop_none, P.binarySymmetric.experiment.observationCharge_zero]
    change ¬ FirstEntryAt (P.input fee hfee) C.val .uncapped accounting source.rule stage.val start sample at he
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right he]

/-- Exact fee identification of the direct kernel with the earlier suffix
kernel. This is charge equality on original entry laws, not a statement
that arbitrary synthetic-startup test paths coincide. -/
theorem directOptionalEntryTest_bayesCharge_eq_sourceKernel (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) (start : ℕ) :
    P.binarySymmetric.experiment.bayesObservationCharge
      (sourceEntrySeedLaw P fee hfee C .uncapped accounting source ν stage start)
      (directOptionalEntryTest P fee hfee source.rule source.measurable_rule stage) =
      P.binarySymmetric.experiment.bayesObservationCharge
        (sourceEntrySeedLaw P fee hfee C .uncapped accounting source ν stage start)
        (optionalSourceEntryTest P fee hfee stage accounting source.rule source.measurable_rule) :=
  (directOptionalEntryTest_bayesCharge_eq_entryStageBill P fee hfee C accounting source ν stage start).trans
    (optionalSourceEntryTest_bayesCharge_eq_entryStageBill P fee hfee C .uncapped accounting source ν stage start).symm

theorem directOptionalEntryTest_bayesCharge_le_fullBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) (start : ℕ) :
    P.binarySymmetric.experiment.bayesObservationCharge
      (sourceEntrySeedLaw P fee hfee C .uncapped accounting source ν stage start)
      (directOptionalEntryTest P fee hfee source.rule source.measurable_rule stage) ≤
      expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν := by
  rw [directOptionalEntryTest_bayesCharge_eq_sourceKernel]
  exact optionalSourceEntryTest_bayesCharge_le_fullBill P fee hfee C .uncapped accounting source ν stage start

/-- Original finite FULL actual bill DERIVES both direct-kernel conditional
ETs. The original source comparison class is not restricted by finite ET. -/
theorem directOptionalEntryTest_finiteET_of_fullBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) (start : ℕ)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    ∀ truth, P.binarySymmetric.experiment.expectedSamples
      (sourceEntrySeedLaw P fee hfee C .uncapped accounting source ν stage start)
      (directOptionalEntryTest P fee hfee source.rule source.measurable_rule stage) truth ≠ ⊤ := by
  have hc := ne_top_of_le_ne_top hfinite
    (directOptionalEntryTest_bayesCharge_le_fullBill P fee hfee C accounting source ν stage start)
  have ho : P.binarySymmetric.experiment.bayesObjective
      (sourceEntrySeedLaw P fee hfee C .uncapped accounting source ν stage start)
      (directOptionalEntryTest P fee hfee source.rule source.measurable_rule stage) 0 ≠ ⊤ := by
    simpa only [BinaryExperiment.bayesObjective, zero_mul, add_zero] using hc
  exact P.binarySymmetric.experiment.bayesObjective_finite_expectedSamples _ _ 0 ho

/-- Direct source kernels account for the entire ORIGINAL observation bill
exactly once. Failed/abandoned/infinite paths and never-entered stages remain. -/
theorem sourceObservationBill_eq_sum_directLocalCharges (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∑ stage : P.sharedInstance.Stage, ∑' start : ℕ,
      P.binarySymmetric.experiment.bayesObservationCharge
        (sourceEntrySeedLaw P fee hfee C .uncapped accounting source ν stage start)
        (directOptionalEntryTest P fee hfee source.rule source.measurable_rule stage)) =
      expectedObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule ν := by
  simp_rw [directOptionalEntryTest_bayesCharge_eq_sourceKernel]
  exact sourceObservationBill_eq_sum_localCharges P fee hfee C .uncapped accounting source ν

end
end PDROC


