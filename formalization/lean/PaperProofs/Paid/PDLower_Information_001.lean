module

public import PaperProofs.Paid.PDROC_EventualEntry_002
public import PaperProofs.Paid.PDROC_FirstFailure_001
public import Mathlib.Algebra.Order.Floor.Extended

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Statistics

namespace PDLower

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem observationCharge_eq_toENNReal (E : BinaryExperiment) (count : ℕ∞) :
    E.observationCharge count = ENNReal.ofReal (E.observationFee : ℝ) * (count : ℝ≥0∞) := by
  by_cases hc : count = ⊤
  · subst count
    have hp : ENNReal.ofReal (E.observationFee : ℝ) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr E.observationFee_real_pos)
    simp only [BinaryExperiment.observationCharge_top, ENat.toENNReal_top, ENNReal.mul_top hp]
  · lift count to ℕ using hc with n
    simp [BinaryExperiment.observationCharge, ENat.toENNReal_coe]

omit [MeasurableSpace Seed] in
theorem runStageObservationBill_eq_count (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hf).World) (stage : P.sharedInstance.Stage) :
    runStageObservationBill (P.input fee hf) C.val mode accounting rule stage sample =
      ENNReal.ofReal (P.reviewFee : ℝ) * (P.paidRunReviewCount fee hf C mode accounting rule sample stage : ℝ≥0∞) := by
  unfold Parameters.paidRunReviewCount runStageObservationBill
  rw [ENat.toENNReal_iSup, ENNReal.mul_iSup]
  rfl

theorem eventualTest_stop_eq_count (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed)
    (sample : Seed × (P.input fee hf).World) (stage : P.sharedInstance.Stage) :
    (PDROC.sourceEventualEntryTest P fee hf source.rule source.measurable_rule stage).rule.stop
      (entryHistorySeedRecord (P.input fee hf) C.val .uncapped accounting source.rule stage sample)
      (worldTapes (P.input fee hf) sample.2 stage) =
      P.paidRunReviewCount fee hf C .uncapped accounting source.rule sample stage := by
  have hcharge : P.binarySymmetric.experiment.observationCharge
      ((PDROC.sourceEventualEntryTest P fee hf source.rule source.measurable_rule stage).rule.stop
        (entryHistorySeedRecord (P.input fee hf) C.val .uncapped accounting source.rule stage sample)
        (worldTapes (P.input fee hf) sample.2 stage)) =
      runStageObservationBill (P.input fee hf) C.val .uncapped accounting source.rule stage sample := by
    cases he : entryHistory (P.input fee hf) C.val .uncapped accounting source.rule stage sample with
    | none =>
      change P.binarySymmetric.experiment.observationCharge
        ((PDROC.sourceEventualEntryTest P fee hf source.rule source.measurable_rule stage).rule.stop
          (sample.1, entryHistory (P.input fee hf) C.val .uncapped accounting source.rule stage sample) _) = _
      rw [he, PDROC.sourceEventualEntryTest_stop_none P fee hf source.rule source.measurable_rule stage sample.1
        (worldTapes (P.input fee hf) sample.2 stage), P.binarySymmetric.experiment.observationCharge_zero]
      exact (PDROC.runStageObservationBill_zero_of_no_entry (P.input fee hf) C.val .uncapped accounting
        source.rule source.legal stage sample he).symm
    | some history =>
      obtain ⟨start, hc, hb, hh⟩ := (entryHistory_some_iff (P.input fee hf) C.val .uncapped accounting source.rule stage sample history).mp he
      change P.binarySymmetric.experiment.observationCharge
        ((PDROC.sourceEventualEntryTest P fee hf source.rule source.measurable_rule stage).rule.stop
          (sample.1, entryHistory (P.input fee hf) C.val .uncapped accounting source.rule stage sample) _) = _
      rw [he, PDROC.sourceEventualEntryTest_stop_some P fee hf source.rule source.measurable_rule stage sample.1 history
        (worldTapes (P.input fee hf) sample.2 stage), ← hh]
      exact PDROC.firstEntry_direct_observationCharge_eq_stageBill P fee hf C accounting source.rule source.legal sample start stage ⟨hc, hb⟩
  rw [observationCharge_eq_toENNReal, runStageObservationBill_eq_count] at hcharge
  apply ENat.toENNReal_inj.mp
  exact (ENNReal.mul_right_inj (ne_of_gt (ENNReal.ofReal_pos.mpr
    (show 0 < (P.reviewFee : ℝ) by exact_mod_cast P.reviewFee_pos))) ENNReal.ofReal_ne_top).mp hcharge

theorem eventualTest_information_eq (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed)
    (sample : Seed × (P.input fee hf).World) (stage : P.sharedInstance.Stage) :
    P.binarySymmetric.stoppedPosteriorInformation
      (PDROC.sourceEventualEntryTest P fee hf source.rule source.measurable_rule stage)
      (entryHistorySeedRecord (P.input fee hf) C.val .uncapped accounting source.rule stage sample,
        worldTapes (P.input fee hf) sample.2 stage) =
      BinarySymmetric.phi (P.paidRunPosteriorError fee hf C .uncapped accounting source.rule sample stage) := by
  let test := PDROC.sourceEventualEntryTest P fee hf source.rule source.measurable_rule stage
  let pair := (entryHistorySeedRecord (P.input fee hf) C.val .uncapped accounting source.rule stage sample,
    worldTapes (P.input fee hf) sample.2 stage)
  have hstop : test.rule.stop pair.1 pair.2 = P.paidRunReviewCount fee hf C .uncapped accounting source.rule sample stage :=
    eventualTest_stop_eq_count P fee hf C accounting source sample stage
  change P.binarySymmetric.stoppedPosteriorInformation test pair = _
  by_cases hzero : P.paidRunReviewCount fee hf C .uncapped accounting source.rule sample stage = 0
  · rw [P.binarySymmetric.stoppedPosteriorInformation_zero_of_stop_zero test pair (hstop.trans hzero),
      P.paidRunPosteriorError_zero fee hf C .uncapped accounting source.rule sample stage hzero, BinarySymmetric.phi_half]
  by_cases htop : P.paidRunReviewCount fee hf C .uncapped accounting source.rule sample stage = ⊤
  · rw [P.binarySymmetric.stoppedPosteriorInformation_of_infinite test pair (hstop.trans htop),
      P.paidRunPosteriorError_infinite fee hf C .uncapped accounting source.rule sample stage htop, BinarySymmetric.phi_zero]
  rw [P.binarySymmetric.stoppedPosteriorInformation_of_finite test pair (by rw [hstop]; exact htop)]
  simp only [Parameters.paidRunPosteriorError, hzero, htop, ↓reduceIte]
  congr 2
  change (⟨(test.rule.stop pair.1 pair.2).toNat, fun k => pair.2 k.val⟩ : P.binarySymmetric.experiment.StoppedWord) = _
  rw [hstop]
  rfl

theorem expectedInformation_eq_auxiliaryTape {Source : Type u} [MeasurableSpace Source]
    (P : Parameters) (ν : Measure Source) [SFinite ν]
    (test : P.binarySymmetric.experiment.AdmissibleRule Source) :
    P.binarySymmetric.expectedPosteriorInformation ν test =
      ∫⁻ sample, P.binarySymmetric.stoppedPosteriorInformation test sample ∂ν.prod (PDROC.auxiliaryTapeLaw P) := by
  rw [PDROC.prod_auxiliaryTapeLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  unfold BinarySymmetric.Parameters.expectedPosteriorInformation
  rw [Fintype.sum_bool, P.binarySymmetric.priorMass_eq_half, P.binarySymmetric.priorMass_eq_half]
  simp only [smul_eq_mul]
  exact add_comm _ _

theorem eventualTest_expectedInformation_eq (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    P.binarySymmetric.expectedPosteriorInformation
      (PDROC.sourceEventualEntrySeedLaw P fee hf C accounting source ν stage)
      (PDROC.sourceEventualEntryTest P fee hf source.rule source.measurable_rule stage) =
      ∫⁻ sample, BinarySymmetric.phi (P.paidRunPosteriorError fee hf C .uncapped accounting source.rule sample stage)
        ∂(P.input fee hf).seededWorldLaw ν := by
  let test := PDROC.sourceEventualEntryTest P fee hf source.rule source.measurable_rule stage
  let joint : Seed × (P.input fee hf).World →
      (Seed × EntryHistory P.sharedInstance) × P.binarySymmetric.experiment.Tape := fun sample =>
    (entryHistorySeedRecord (P.input fee hf) C.val .uncapped accounting source.rule stage sample,
      (sample.2 stage).2)
  have hjoint : Measurable joint :=
    (measurable_entryHistorySeedRecord (P.input fee hf) C.val .uncapped accounting source.rule source.measurable_rule stage).prodMk
      ((PDROC.measurable_worldTape (P.input fee hf) stage).comp measurable_snd)
  have hlaw : ((P.input fee hf).seededWorldLaw ν).map joint =
      (PDROC.sourceEventualEntrySeedLaw P fee hf C accounting source ν stage).prod (PDROC.auxiliaryTapeLaw P) :=
    PDROC.sourceEventualEntry_joint_directTape P fee hf C accounting source ν stage
  rw [expectedInformation_eq_auxiliaryTape, ← hlaw,
    lintegral_map (P.binarySymmetric.measurable_stoppedPosteriorInformation test) hjoint]
  apply lintegral_congr
  intro sample
  exact eventualTest_information_eq P fee hf C accounting source sample stage

theorem survivingInformationLower_uncapped (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ENNReal.ofReal P.a * (∑ stage : P.sharedInstance.Stage,
      ∫⁻ sample, (P.survivingEntry fee hf C .uncapped accounting source.rule stage).indicator
        (fun sample => BinarySymmetric.phi (P.paidRunPosteriorError fee hf C .uncapped accounting source.rule sample stage)) sample
          ∂(P.input fee hf).seededWorldLaw ν) ≤
      expectedObservationBill (P.input fee hf) C.val .uncapped accounting source.rule ν := by
  by_cases htop : expectedObservationBill (P.input fee hf) C.val .uncapped accounting source.rule ν = ⊤
  · rw [htop]
    exact le_top
  have hsum := PDROC.sourceObservationBill_eq_sum_eventualCharges P fee hf C accounting source ν
  have hstage (stage : P.sharedInstance.Stage) :
      P.binarySymmetric.experiment.bayesObservationCharge
        (PDROC.sourceEventualEntrySeedLaw P fee hf C accounting source ν stage)
        (PDROC.sourceEventualEntryTest P fee hf source.rule source.measurable_rule stage) =
      ENNReal.ofReal P.a * ∫⁻ sample, BinarySymmetric.phi
        (P.paidRunPosteriorError fee hf C .uncapped accounting source.rule sample stage)
          ∂(P.input fee hf).seededWorldLaw ν := by
    have hc := Finset.single_le_sum (f := fun stage : P.sharedInstance.Stage =>
      P.binarySymmetric.experiment.bayesObservationCharge
        (PDROC.sourceEventualEntrySeedLaw P fee hf C accounting source ν stage)
        (PDROC.sourceEventualEntryTest P fee hf source.rule source.measurable_rule stage))
      (fun _ _ => zero_le) (Finset.mem_univ stage)
    rw [hsum] at hc
    rw [P.binarySymmetric.bayesObservationCharge_eq_posteriorInformation_of_finite_charge _ _
      (ne_top_of_le_ne_top htop hc), eventualTest_expectedInformation_eq]
    rfl
  calc
    _ ≤ ENNReal.ofReal P.a * (∑ stage : P.sharedInstance.Stage,
        ∫⁻ sample, BinarySymmetric.phi (P.paidRunPosteriorError fee hf C .uncapped accounting source.rule sample stage)
          ∂(P.input fee hf).seededWorldLaw ν) := by
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro stage _
      apply lintegral_mono
      intro sample
      exact Set.indicator_le_self (s := P.survivingEntry fee hf C .uncapped accounting source.rule stage)
        (f := fun sample => BinarySymmetric.phi (P.paidRunPosteriorError fee hf C .uncapped accounting source.rule sample stage)) sample
    _ = ∑ stage : P.sharedInstance.Stage, P.binarySymmetric.experiment.bayesObservationCharge
        (PDROC.sourceEventualEntrySeedLaw P fee hf C accounting source ν stage)
        (PDROC.sourceEventualEntryTest P fee hf source.rule source.measurable_rule stage) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun stage _ => (hstage stage).symm)
    _ = _ := hsum

theorem survivingInformationLower (P : Parameters) : P.SurvivingInformationLower.{u} := by
  intro fee hf C mode accounting Seed m
  let : MeasurableSpace Seed := m
  intro ν hν
  let : IsProbabilityMeasure ν := hν
  intro policy
  have h := survivingInformationLower_uncapped P fee hf C accounting
    (PDROC.uncappedSourcePolicy (P.input fee hf) C.val mode accounting policy) ν
  have hr : run (P.input fee hf) C.val .uncapped accounting
      (PDROC.uncappedSourcePolicy (P.input fee hf) C.val mode accounting policy).rule =
      run (P.input fee hf) C.val mode accounting policy.rule := by
    funext sample n
    exact PDROC.uncappedSourcePolicy_run (P.input fee hf) C.val mode accounting policy sample n
  have hentry (stage : P.sharedInstance.Stage) (sample : Seed × (P.input fee hf).World) :
      entryHistory (P.input fee hf) C.val .uncapped accounting
        (PDROC.uncappedSourcePolicy (P.input fee hf) C.val mode accounting policy).rule stage sample =
      entryHistory (P.input fee hf) C.val mode accounting policy.rule stage sample := by
    cases he : entryHistory (P.input fee hf) C.val mode accounting policy.rule stage sample with
    | none =>
      apply (entryHistory_none_iff _ _ _ _ _ _ _).mpr
      intro hn
      apply (entryHistory_none_iff _ _ _ _ _ _ _).mp he
      simpa only [hr] using hn
    | some history =>
      apply (entryHistory_some_iff _ _ _ _ _ _ _ _).mpr
      simpa only [hr] using (entryHistory_some_iff _ _ _ _ _ _ _ _).mp he
  have hcount (sample : Seed × (P.input fee hf).World) (stage : P.sharedInstance.Stage) :
      P.paidRunReviewCount fee hf C .uncapped accounting
        (PDROC.uncappedSourcePolicy (P.input fee hf) C.val mode accounting policy).rule sample stage =
      P.paidRunReviewCount fee hf C mode accounting policy.rule sample stage := by
    unfold Parameters.paidRunReviewCount
    simp only [hr]
  have hposterior (sample : Seed × (P.input fee hf).World) (stage : P.sharedInstance.Stage) :
      P.paidRunPosteriorError fee hf C .uncapped accounting
        (PDROC.uncappedSourcePolicy (P.input fee hf) C.val mode accounting policy).rule sample stage =
      P.paidRunPosteriorError fee hf C mode accounting policy.rule sample stage := by
    exact congrArg (fun count : ℕ∞ => if count = 0 then (1 / 2 : ℝ) else if count = ⊤ then 0 else
      P.binarySymmetric.wordPosteriorError ⟨count.toNat, fun k => (sample.2 stage).2 k.val⟩) (hcount sample stage)
  simpa only [Parameters.survivingEntry, Parameters.actualSurvivingEntry,
    Parameters.nextStageFilledEntry, hentry, hposterior,
    expectedObservationBill, runObservationBill, hr] using h

end PDLower
