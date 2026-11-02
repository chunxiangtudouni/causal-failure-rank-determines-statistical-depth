module
public import PaperProofs.Paid.PDROC_LocalRecord_016

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

theorem expectedSamples_pullbackSeedTest (E : BinaryExperiment) {SeedA : Type u} {SeedB : Type v}
    [MeasurableSpace SeedA] [MeasurableSpace SeedB] (ν : Measure SeedA)
    (test : E.AdmissibleRule SeedB) (f : SeedA → SeedB) (hf : Measurable f) (truth : Bool) :
    E.expectedSamples ν (pullbackSeedTest E test f hf) truth = E.expectedSamples (ν.map f) test truth := by
  have hlaw := Measure.map_prod_map ν (E.tapeLaw truth) hf (measurable_id : Measurable (id : E.Tape → E.Tape))
  rw [Measure.map_id] at hlaw
  have hcount : Measurable (fun sample : SeedB × E.Tape => BinaryExperiment.sampleCountENNReal
      (test.rule.stop sample.1 sample.2)) := (measurable_of_countable BinaryExperiment.sampleCountENNReal).comp test.measurable_stop
  have hp : Measurable (Prod.map f (id : E.Tape → E.Tape)) := hf.prodMap measurable_id
  unfold BinaryExperiment.expectedSamples BinaryExperiment.conditionalLaw
  rw [hlaw, lintegral_map hcount hp]
  rfl

theorem bayesObservationCharge_pullbackSeedTest (E : BinaryExperiment) {SeedA : Type u} {SeedB : Type v}
    [MeasurableSpace SeedA] [MeasurableSpace SeedB] (ν : Measure SeedA)
    (test : E.AdmissibleRule SeedB) (f : SeedA → SeedB) (hf : Measurable f) :
    E.bayesObservationCharge ν (pullbackSeedTest E test f hf) = E.bayesObservationCharge (ν.map f) test := by
  unfold BinaryExperiment.bayesObservationCharge
  apply Finset.sum_congr rfl
  intro truth _
  rw [E.expectedObservationCharge_eq, E.expectedObservationCharge_eq,
    expectedSamples_pullbackSeedTest]

section
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The actual original first-entry source law, augmented only with its
public entry history. The entire original source coordinate is preserved;
there is no normalization, conditional-probability oracle, or future truth. -/
noncomputable def sourceEntryDrawSeedLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) (stage : P.sharedInstance.Stage) (start : ℕ) :
    Measure ((Seed × Option (Startup P.sharedInstance)) × List (VisibleEvent P.sharedInstance)) :=
  (sourceEntrySeedLaw P fee hfee C .uncapped accounting source ν stage start).map (sourceEntryHistorySeed P)

instance sourceEntryDrawSeedLaw_probability (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) (start : ℕ) :
    IsProbabilityMeasure (sourceEntryDrawSeedLaw P fee hfee C accounting source ν stage start) := by
  unfold sourceEntryDrawSeedLaw
  infer_instance

/-- Original finite FULL expected actual bill derives both finite ETs of
the actual direct draw kernel used by the simulator, including off-entry
blind completion. It is not an added qualification of source Policy. -/
theorem sourceEntryDraw_finiteET_of_fullBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) (start : ℕ)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    ∀ truth, P.binarySymmetric.experiment.expectedSamples
      (sourceEntryDrawSeedLaw P fee hfee C accounting source ν stage start)
      (simulatorLocalTest P fee hfee (sourceForOptionalEntry P source.rule)
        (measurable_sourceForOptionalEntry P source.rule source.measurable_rule) stage) truth ≠ ⊤ := by
  intro truth
  unfold sourceEntryDrawSeedLaw
  rw [← expectedSamples_pullbackSeedTest P.binarySymmetric.experiment
    (sourceEntrySeedLaw P fee hfee C .uncapped accounting source ν stage start)
    (simulatorLocalTest P fee hfee (sourceForOptionalEntry P source.rule)
      (measurable_sourceForOptionalEntry P source.rule source.measurable_rule) stage)
    (sourceEntryHistorySeed P) (measurable_sourceEntryHistorySeed P) truth]
  exact directOptionalEntryTest_finiteET_of_fullBill P fee hfee C accounting source ν stage start hfinite truth

/-- Exact mean Cm on the complete actual source-entry/draw law. The finite
ET premise of D03 is discharged by the original finite FULL actual bill. -/
theorem sourceEntryDraw_endpointCharge_mean_of_fullBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) (start : ℕ)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    (∫⁻ record : ((Seed × Option (Startup P.sharedInstance)) × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance,
      ENNReal.ofReal (P.binarySymmetric.endpointCharge record.2.record.level : ℝ)
        ∂simulatorDrawLaw P fee hfee (sourceForOptionalEntry P source.rule)
          (measurable_sourceForOptionalEntry P source.rule source.measurable_rule) stage
            (sourceEntryDrawSeedLaw P fee hfee C accounting source ν stage start)) =
      P.binarySymmetric.experiment.bayesObservationCharge
        (sourceEntrySeedLaw P fee hfee C .uncapped accounting source ν stage start)
        (directOptionalEntryTest P fee hfee source.rule source.measurable_rule stage) := by
  rw [← simulatorDrawLaw_endpointCharge_mean P fee hfee (sourceForOptionalEntry P source.rule)
    (measurable_sourceForOptionalEntry P source.rule source.measurable_rule) stage
    (sourceEntryDrawSeedLaw P fee hfee C accounting source ν stage start)
    (sourceEntryDraw_finiteET_of_fullBill P fee hfee C accounting source ν stage start hfinite)]
  exact (bayesObservationCharge_pullbackSeedTest P.binarySymmetric.experiment
    (sourceEntrySeedLaw P fee hfee C .uncapped accounting source ν stage start)
    (simulatorLocalTest P fee hfee (sourceForOptionalEntry P source.rule)
      (measurable_sourceForOptionalEntry P source.rule source.measurable_rule) stage)
    (sourceEntryHistorySeed P) (measurable_sourceEntryHistorySeed P)).symm

/-- Sum of the REAL source-record Cm means is exactly the original complete
observation expectation. Abandonment and failed paths retain their original
observations; a replacement may skip observation on abandoning records. -/
theorem sourceObservationBill_eq_sum_drawEndpointMeans (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    (∑ stage : P.sharedInstance.Stage, ∑' start : ℕ,
      ∫⁻ record : ((Seed × Option (Startup P.sharedInstance)) × List (VisibleEvent P.sharedInstance)) × SimulatorDraw P.sharedInstance,
        ENNReal.ofReal (P.binarySymmetric.endpointCharge record.2.record.level : ℝ)
          ∂simulatorDrawLaw P fee hfee (sourceForOptionalEntry P source.rule)
            (measurable_sourceForOptionalEntry P source.rule source.measurable_rule) stage
              (sourceEntryDrawSeedLaw P fee hfee C accounting source ν stage start)) =
      expectedObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule ν := by
  simp_rw [sourceEntryDraw_endpointCharge_mean_of_fullBill P fee hfee C accounting source ν _ _ hfinite]
  exact sourceObservationBill_eq_sum_directLocalCharges P fee hfee C accounting source ν

end
end PDROC
