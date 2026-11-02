module

public import PaperProofs.Retained.PDROC_RetainedReturn_001
public import PaperProofs.Common.ReferenceTermination

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained
open PaperProofs.Statistics MeasureTheory

namespace PDROC.RetainedReturn

variable {I : Instance}

/-- A sample-specific analysis bound on actual requests. This does not cap
or modify the original ideal policy, or reset an entry ledger or history. -/
theorem retainedRun_halts_of_posteriorStops_finite (input : StatisticalInput I)
    (C : Contract I) (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2)
    (sample : Unit × input.World)
    (finite : ∀ (stage : I.Stage) (p : ℚ), 0 < p → p ≤ 1 / 4 →
      (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 ≠ ⊤) :
    ∃ n, (run input C .uncapped accounting (retainedRule input budget none) sample n).halted = true := by
  classical
  let quota (stage : I.Stage) : ℕ :=
    match entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample with
    | none => 0
    | some history => match PRetRiskMassFlow.entryTarget I budget stage history with
      | none => 0
      | some p => ((input.experiment stage).posteriorThresholdStop p (sample.2 stage).2).toNat
  have gate : ∀ (n : ℕ) (state : State I),
      Prefix input C .uncapped accounting (retainedRule input budget none) sample.1
        (input.truthAt sample.2) (worldTapes input sample.2) n state →
      state.halted = false → ∀ stage : I.Stage,
        retainedRule input budget none sample.1 state.history = .review stage →
          state.ledger.reviews stage < (quota stage : ℕ∞) := by
    intro n state path active stage selected
    obtain ⟨history, p, entered, target, strict⟩ := PRetRiskMassFlow.prefix_review_realization
      input C hretained accounting budget positive small sample path active stage selected
    have valid := PRetRiskMassFlow.entryTarget_valid budget stage history p target
    have stopFinite := finite stage p valid.1 valid.2
    simpa only [quota, entered, target, ENat.natCast_toNat stopFinite] using strict
  by_contra never
  let bound := reviewBoundedActionBound I quota
  have active : (run input C .uncapped accounting (retainedRule input budget none)
      sample (bound + 1)).halted = false :=
    Bool.eq_false_iff.mpr (not_exists.mp never (bound + 1))
  have path := run_prefix_of_active input C .uncapped accounting (retainedRule input budget none)
    (retainedRule_uncapped_legal input C hretained accounting budget none) sample (bound + 1) active
  have bounded := prefix_reviews_le_of_review_gate input C .uncapped accounting (retainedRule input budget none)
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) quota gate path
  have length := prefix_length_le_of_reviews_bounded input C .uncapped accounting
    (retainedRule input budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2)
    path quota bounded
  change bound + 1 ≤ bound at length
  omega

/-- Almost-sure returned-action termination of the unchanged original
retained ideal policy, for every original early-retained contract. -/
theorem idealPolicy_ae_halts (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2) :
    ∀ᵐ sample ∂input.seededWorldLaw (Measure.dirac ()),
      ∃ n, (run input C .uncapped accounting (idealPolicy input C hretained accounting budget).rule
        sample n).halted = true := by
  filter_upwards [all_posteriorStops_ae_finite input] with sample finite
  exact retainedRun_halts_of_posteriorStops_finite input C hretained accounting budget positive small sample finite

theorem idealPolicy_nontermination_measure_zero (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2) :
    input.seededWorldLaw (Measure.dirac ()) {sample : Unit × input.World |
      ¬ ∃ n, (run input C .uncapped accounting (idealPolicy input C hretained accounting budget).rule
        sample n).halted = true} = 0 :=
  ae_iff.mp (idealPolicy_ae_halts input C hretained accounting budget positive small)

end PDROC.RetainedReturn
