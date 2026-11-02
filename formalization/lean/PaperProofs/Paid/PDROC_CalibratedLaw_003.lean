module

public import PaperProofs.Paid.PDROC_CalibratedLaw_002
public import PaperProofs.Paid.PDROC_MenuExpected_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Statistics
open scoped ENNReal

namespace PDROC.CalibratedLaw

open PDROC.CalibratedRuntime

def localSampleProjection (P : Parameters) (level : ℕ)
    (sample : StageSeed P × P.experiment.Tape) : (Bool × Bool) × P.experiment.Tape :=
  (localCalibrationSeed P level sample.1, sample.2)

theorem measurable_localSampleProjection (P : Parameters) (level : ℕ) :
    Measurable (localSampleProjection P level) :=
  ((measurable_of_countable (localCalibrationSeed P level)).comp measurable_fst).prodMk measurable_snd

theorem conditionalLaw_localSampleProjection (P : Parameters) (level : ℕ)
    (valid : level ≤ P.certificate.M) (truth : Bool) :
    (P.experiment.conditionalLaw (stageSeedLaw P) truth).map (localSampleProjection P level) =
      P.experiment.conditionalLaw (P.calibrationSeedLaw level) truth := by
  have hprod := Measure.map_prod_map (stageSeedLaw P) (P.experiment.tapeLaw truth)
    (measurable_of_countable (localCalibrationSeed P level)) measurable_id
  rw [localCalibrationSeed_law P level valid, Measure.map_id] at hprod
  exact hprod.symm

theorem calibratedStageTest_conditionalError (P : Parameters) (level : ℕ)
    (valid : level ≤ P.certificate.M) (truth : Bool) :
    P.experiment.conditionalError (stageSeedLaw P) (calibratedStageTest P level) truth =
      ENNReal.ofReal (P.binarySymmetric.endpointError level : ℝ) := by
  let error : Set ((Bool × Bool) × P.experiment.Tape) :=
    {sample | (P.calibratedTest level).rule.decision sample.1 sample.2 ≠ truth}
  have hm : MeasurableSet error :=
    ((P.calibratedTest level).measurable_decision (measurableSet_singleton truth)).compl
  calc
    _ = P.experiment.conditionalLaw (stageSeedLaw P) truth
        ((localSampleProjection P level) ⁻¹' error) := rfl
    _ = ((P.experiment.conditionalLaw (stageSeedLaw P) truth).map (localSampleProjection P level)) error :=
      (Measure.map_apply (measurable_localSampleProjection P level) hm).symm
    _ = P.experiment.conditionalError (P.calibrationSeedLaw level) (P.calibratedTest level) truth := by
      rw [conditionalLaw_localSampleProjection P level valid truth]
      rfl
    _ = _ := calibrated_conditionalError P level valid truth

theorem calibratedStageTest_conditionalCharge (P : Parameters) (level : ℕ)
    (valid : level ≤ P.certificate.M) (truth : Bool) :
    P.experiment.expectedObservationCharge (stageSeedLaw P) (calibratedStageTest P level) truth =
      P.experiment.expectedObservationCharge (P.calibrationSeedLaw level) (P.calibratedTest level) truth := by
  let charge := fun sample : (Bool × Bool) × P.experiment.Tape =>
    P.experiment.observationCharge ((P.calibratedTest level).rule.stop sample.1 sample.2)
  have hm : Measurable charge := (measurable_of_countable P.experiment.observationCharge).comp
    (P.calibratedTest level).measurable_stop
  calc
    _ = ∫⁻ sample, charge (localSampleProjection P level sample)
        ∂P.experiment.conditionalLaw (stageSeedLaw P) truth := rfl
    _ = ∫⁻ sample, charge sample
        ∂(P.experiment.conditionalLaw (stageSeedLaw P) truth).map (localSampleProjection P level) :=
      (lintegral_map hm (measurable_localSampleProjection P level)).symm
    _ = _ := by
      rw [conditionalLaw_localSampleProjection P level valid truth]
      rfl

theorem calibratedStageTest_bayesError (P : Parameters) (level : ℕ)
    (valid : level ≤ P.certificate.M) :
    P.experiment.bayesError (stageSeedLaw P) (calibratedStageTest P level) =
      ENNReal.ofReal (P.binarySymmetric.endpointError level : ℝ) := by
  unfold BinaryExperiment.bayesError
  simp_rw [calibratedStageTest_conditionalError P level valid]
  rw [← Finset.sum_mul, P.experiment.priorMass_sum, one_mul]

theorem calibratedStageTest_bayesCharge_le_four (P : Parameters) (level : ℕ)
    (valid : level ≤ P.certificate.M) :
    P.experiment.bayesObservationCharge (stageSeedLaw P) (calibratedStageTest P level) ≤
      4 * ENNReal.ofReal (P.binarySymmetric.endpointCharge level : ℝ) := by
  unfold BinaryExperiment.bayesObservationCharge
  calc
    _ ≤ ∑ truth : Bool, P.experiment.priorMass truth *
        (4 * ENNReal.ofReal (P.binarySymmetric.endpointCharge level : ℝ)) := by
      apply Finset.sum_le_sum
      intro truth _member
      rw [calibratedStageTest_conditionalCharge P level valid truth]
      exact mul_le_mul' le_rfl (calibrated_conditionalCharge_le_four P level valid truth)
    _ = _ := by rw [← Finset.sum_mul, P.experiment.priorMass_sum, one_mul]

abbrev Head (P : Parameters) := StageSeed P × (Bool × P.experiment.Tape)

noncomputable def headLaw (P : Parameters) : Measure (Head P) :=
  (stageSeedLaw P).prod (PDMenu.menuAnalysisStageLaw P)

instance headLaw_probability (P : Parameters) : IsProbabilityMeasure (headLaw P) := by
  unfold headLaw
  infer_instance

def correctGate (P : Parameters) (level : ℕ) : Set (Head P) :=
  BellmanExpectation.headCorrectGate (P.freshInput 1 0 0 (by decide)) PDMenu.menuAnalysisHead
    (calibratedStageTest P level)

theorem measurableSet_correctGate (P : Parameters) (level : ℕ) : MeasurableSet (correctGate P level) :=
  BellmanExpectation.measurableSet_headCorrectGate _ _ _

theorem wrong_mass (P : Parameters) (level : ℕ) (valid : level ≤ P.certificate.M) :
    headLaw P (correctGate P level)ᶜ = ENNReal.ofReal (P.binarySymmetric.endpointError level : ℝ) :=
  (BellmanExpectation.wrongMass_eq_bayesError (P.freshInput 1 0 0 (by decide)) PDMenu.menuAnalysisHead
    (stageSeedLaw P) (calibratedStageTest P level)).trans (calibratedStageTest_bayesError P level valid)

theorem correct_mass (P : Parameters) (level : ℕ) (valid : level ≤ P.certificate.M) :
    headLaw P (correctGate P level) = ENNReal.ofReal (1 - (P.binarySymmetric.endpointError level : ℝ)) := by
  have hm := (measurableSet_correctGate P level).compl
  have hpos : 0 ≤ (P.binarySymmetric.endpointError level : ℝ) := by
    exact_mod_cast (P.binarySymmetric.endpointError_pos level).le
  calc
    _ = headLaw P ((correctGate P level)ᶜ)ᶜ := by rw [compl_compl]
    _ = 1 - headLaw P (correctGate P level)ᶜ := by rw [measure_compl hm (measure_ne_top _ _), measure_univ]
    _ = _ := by rw [wrong_mass P level valid, ENNReal.ofReal_sub _ hpos, ENNReal.ofReal_one]

noncomputable def headCharge (P : Parameters) (level : ℕ) (sample : Head P) : ℝ≥0∞ :=
  P.experiment.observationCharge ((calibratedStageTest P level).rule.stop sample.1 sample.2.2)

theorem measurable_headCharge (P : Parameters) (level : ℕ) : Measurable (headCharge P level) :=
  (measurable_of_countable P.experiment.observationCharge).comp
    ((calibratedStageTest P level).measurable_stop.comp (measurable_fst.prodMk measurable_snd.snd))

theorem headCharge_integral_le_four (P : Parameters) (level : ℕ) (valid : level ≤ P.certificate.M) :
    (∫⁻ sample, headCharge P level sample ∂headLaw P) ≤
      4 * ENNReal.ofReal (P.binarySymmetric.endpointCharge level : ℝ) := by
  let input := P.freshInput 1 0 0 (by decide)
  let projection : StageSeed P × input.World → Head P := fun sample => (sample.1, sample.2 PDMenu.menuAnalysisHead)
  have hm : Measurable projection := measurable_fst.prodMk ((measurable_pi_apply PDMenu.menuAnalysisHead).comp measurable_snd)
  have hmap : (input.seededWorldLaw (stageSeedLaw P)).map projection = headLaw P :=
    BellmanExpectation.localHeadSeed_law input PDMenu.menuAnalysisHead (stageSeedLaw P)
  have h := lintegral_map (μ := input.seededWorldLaw (stageSeedLaw P)) (measurable_headCharge P level) hm
  rw [hmap] at h
  have hb := bayesObservationCharge_eq_seededWorld_integral input PDMenu.menuAnalysisHead (stageSeedLaw P)
    (calibratedStageTest P level)
  exact (h.trans hb.symm).le.trans (calibratedStageTest_bayesCharge_le_four P level valid)

theorem head_stop_finite (P : Parameters) (level : ℕ) (sample : Head P) :
    (calibratedStageTest P level).rule.stop sample.1 sample.2.2 ≠ ⊤ := by
  rw [calibratedStageTest_stop]
  exact calibrated_stop_ne_top P level _ _

end PDROC.CalibratedLaw
