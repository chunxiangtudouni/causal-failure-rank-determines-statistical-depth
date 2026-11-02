module

public import PaperProofs.Paid.BridgeClaims
public import PaperProofs.Paid.PDLower_BlindTruthLaw_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Paid.PA17D31WitnessLaw004

open Common Common.Native

theorem input_priorMass (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (bit : Bool) :
    ((P.input fee hfee).experiment stage).priorMass bit = ENNReal.ofReal (1 / 2 : ℝ) := by
  cases bit <;>
    norm_num [Statistics.BinaryExperiment.priorMass, Statistics.BinaryExperiment.priorReal,
      Statistics.BinaryExperiment.prior, Parameters.input, Parameters.experiment]

theorem blindErrorCount_eq_stages_iff (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (sample : Unit × (P.input fee hfee).World) :
    P.blindErrorCount fee hfee sample = P.certificate.stages ↔
      ∀ stage, (sample.2 stage).1 = true := by
  classical
  have hcard : (Finset.univ : Finset P.sharedInstance.Stage).card = P.certificate.stages := by
    calc
      (Finset.univ : Finset P.sharedInstance.Stage).card = Fintype.card P.sharedInstance.Stage := Finset.card_univ
      _ = P.sharedInstance.stageCount := Fintype.card_fin _
      _ = P.certificate.stages := P.stageCount_eq
  rw [Parameters.blindErrorCount, ← hcard, Finset.card_filter_eq_iff]
  simp

def trueEvent (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage) :
    Set (Unit × (P.input fee hfee).World) := {sample | (sample.2 stage).1 = true}

theorem measurableSet_trueEvent (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) : MeasurableSet (trueEvent P fee hfee stage) :=
  measurableSet_eq_fun (((P.input fee hfee).measurable_truthAt stage).comp measurable_snd)
    measurable_const

theorem trueEvent_mass (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) :
    (P.input fee hfee).seededWorldLaw (Measure.dirac ()) (trueEvent P fee hfee stage) =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  let input := P.input fee hfee
  have hs : trueEvent P fee hfee stage =
      Set.univ ×ˢ {world : input.World | input.truthAt world stage = true} := by
    ext sample
    simp [trueEvent, StatisticalInput.truthAt]
  rw [StatisticalInput.seededWorldLaw, hs, Measure.prod_prod, measure_univ, one_mul,
    StatisticalInput.worldLaw_truth]
  exact input_priorMass P fee hfee stage true

theorem blindErrorCount_sum (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (sample : Unit × (P.input fee hfee).World) :
    (P.blindErrorCount fee hfee sample : ℝ≥0∞) =
      ∑ stage : P.sharedInstance.Stage,
        (trueEvent P fee hfee stage).indicator (fun _ => (1 : ℝ≥0∞)) sample := by
  classical
  rw [Parameters.blindErrorCount, Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter,
    trueEvent, Set.indicator, Set.mem_ofPred_eq]
  apply Finset.sum_congr rfl
  intro stage _
  by_cases h : (sample.2 stage).1 = true <;> simp only [h, ↓reduceIte]

/-- The untruncated mean is derived from the actual world coordinate laws. -/
theorem lintegral_blindErrorCount (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    (∫⁻ sample : Unit × (P.input fee hfee).World,
      (P.blindErrorCount fee hfee sample : ℝ≥0∞)
      ∂(P.input fee hfee).seededWorldLaw (Measure.dirac ())) =
      ENNReal.ofReal ((P.certificate.stages : ℝ) / 2) := by
  simp_rw [blindErrorCount_sum]
  rw [lintegral_finsetSum Finset.univ (fun stage _ =>
    measurable_const.indicator (measurableSet_trueEvent P fee hfee stage))]
  simp_rw [lintegral_indicator_const (measurableSet_trueEvent P fee hfee _),
    one_mul, trueEvent_mass]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card P.sharedInstance.Stage = P.certificate.stages := by
    simp only [Parameters.sharedInstance, Instance.Stage, List.length_replicate, Fintype.card_fin]
  rw [hcard, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The frozen DLower complete-assignment law supplies the original all-error
event probability on the actual Unit-seeded world law. -/
theorem original_full_error_mass (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (hdelta : P.certificate.risk = (1 / 2 : ℚ) ^ P.certificate.stages) :
    (P.input fee hfee).seededWorldLaw (Measure.dirac ())
      {sample | P.blindErrorCount fee hfee sample = P.certificate.stages} = P.targetRisk := by
  have heq : {sample : Unit × (P.input fee hfee).World |
      P.blindErrorCount fee hfee sample = P.certificate.stages} =
      Set.univ ×ˢ {world | (P.input fee hfee).truthAt world = (fun _ => true)} := by
    ext sample
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and,
      blindErrorCount_eq_stages_iff]
    exact funext_iff.symm
  rw [StatisticalInput.seededWorldLaw, heq, Measure.prod_prod, measure_univ, one_mul,
    PDLower.paid_truth_assignment_mass]
  simp only [Parameters.targetRisk, hdelta]

theorem measurable_blindErrorCount (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    Measurable (P.blindErrorCount fee hfee) := by
  let f : (P.sharedInstance.Stage → Bool) → ℕ := fun truth =>
    (Finset.univ.filter (fun stage => truth stage = true)).card
  have hm : Measurable (fun sample : Unit × (P.input fee hfee).World =>
      fun stage : P.sharedInstance.Stage => (sample.2 stage).1) :=
    measurable_pi_iff.mpr fun stage =>
      ((P.input fee hfee).measurable_truthAt stage).comp measurable_snd
  exact (measurable_of_countable f).comp hm

noncomputable def truncatedErrorCount (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (sample : Unit × (P.input fee hfee).World) : ℝ≥0∞ :=
  if P.blindErrorCount fee hfee sample = P.certificate.stages then 0
  else (P.blindErrorCount fee hfee sample : ℝ≥0∞)

theorem measurable_truncatedErrorCount (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    Measurable (truncatedErrorCount P fee hfee) :=
  (measurable_of_countable (fun count : ℕ =>
    if count = P.certificate.stages then (0 : ℝ≥0∞) else (count : ℝ≥0∞))).comp
      (measurable_blindErrorCount P fee hfee)

/-- The complete-assignment probability is an explicit argument so the
independent DLower truth-law proof can be reused without duplicating it. -/
theorem lintegral_truncatedErrorCount (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (delta : ℝ) (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1 / 2)
    (hmass : (P.input fee hfee).seededWorldLaw (Measure.dirac ())
      {sample | P.blindErrorCount fee hfee sample = P.certificate.stages} = ENNReal.ofReal delta) :
    (∫⁻ sample, truncatedErrorCount P fee hfee sample
      ∂(P.input fee hfee).seededWorldLaw (Measure.dirac ())) =
      ENNReal.ofReal ((P.certificate.stages : ℝ) / 2 - P.certificate.stages * delta) := by
  let full : Set (Unit × (P.input fee hfee).World) :=
    {sample | P.blindErrorCount fee hfee sample = P.certificate.stages}
  have hs : MeasurableSet full := measurableSet_eq_fun
    (measurable_blindErrorCount P fee hfee) measurable_const
  have hsplit (sample : Unit × (P.input fee hfee).World) :
      (P.blindErrorCount fee hfee sample : ℝ≥0∞) =
        truncatedErrorCount P fee hfee sample +
          full.indicator (fun _ => (P.certificate.stages : ℝ≥0∞)) sample := by
    by_cases hfull : P.blindErrorCount fee hfee sample = P.certificate.stages
    · simp [truncatedErrorCount, full, hfull]
    · simp [truncatedErrorCount, full, hfull]
  have hmean := lintegral_blindErrorCount P fee hfee
  simp_rw [hsplit] at hmean
  rw [lintegral_add_left (measurable_truncatedErrorCount P fee hfee),
    lintegral_indicator_const hs, hmass] at hmean
  have hN : 0 ≤ (P.certificate.stages : ℝ) := Nat.cast_nonneg _
  have hproduct : (P.certificate.stages : ℝ≥0∞) * ENNReal.ofReal delta =
      ENNReal.ofReal (P.certificate.stages * delta) := by
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_mul hN]
  rw [hproduct] at hmean
  apply (ENNReal.add_left_inj ENNReal.ofReal_ne_top).mp
  rw [hmean, ← ENNReal.ofReal_add (by nlinarith) (mul_nonneg hN hdelta)]
  congr 1
  ring

end PaperProofs.Paid.PA17D31WitnessLaw004
