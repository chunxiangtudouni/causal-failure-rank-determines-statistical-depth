module

public import PaperProofs.Retained.PDROC_RetainedEnvelopeRun_007
public import PaperProofs.Statistics.ReferenceBudgetMassTelescope

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics
open PaperProofs.Retained.PRetObservationEnvelope119
open MeasureTheory
open scoped ENNReal BigOperators

namespace PDROC.RetainedEnvelopeRun

variable {I : Instance}

noncomputable def stageObservationMean (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (next : ℕ) : ℝ≥0∞ :=
  if h : next < I.stageCount then
    ∫⁻ sample, runStageObservationBill input C .uncapped accounting
      (retainedRule input budget none) ⟨next, h⟩ sample ∂input.seededWorldLaw (Measure.dirac ())
  else 0

theorem expectedObservationBill_eq_sum_stageMeans (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I) (budget : ℚ) :
    expectedObservationBill input C .uncapped accounting
      (idealPolicy input C hretained accounting budget).rule (Measure.dirac ()) =
      ∑ next ∈ Finset.range I.stageCount, stageObservationMean input C accounting budget next := by
  change expectedObservationBill input C .uncapped accounting (retainedRule input budget none)
    (Measure.dirac ()) = _
  rw [expectedObservationBill_eq_sum_stage input C .uncapped accounting
    (retainedRule input budget none) (retainedRule_uncapped_legal input C hretained accounting budget none)
    (measurable_of_countable _) (Measure.dirac ()), Finset.sum_fin_eq_sum_range]
  rfl

/-- The original retained execution is dominated by the unchanged119
envelope at its actual initial half-budget. All observation bills retain
their suprema over genuine prefixes, including infinity and failure paths. -/
theorem expectedObservationBill_le_observationEnvelope (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2) :
    expectedObservationBill input C .uncapped accounting
      (idealPolicy input C hretained accounting budget).rule (Measure.dirac ()) ≤
      observationEnvelope input 0 ∅ (budget / 2) := by
  have drift : ∀ next, next < I.stageCount → stageObservationMean input C accounting budget next +
      (∫⁻ sample, entryEnvelopePotential input C accounting budget (next + 1) sample
        ∂input.seededWorldLaw (Measure.dirac ())) ≤
      (∫⁻ sample, entryEnvelopePotential input C accounting budget next sample
        ∂input.seededWorldLaw (Measure.dirac ())) := by
    intro next hn
    have stageDrift := stageEnvelope_drift input C hretained accounting budget positive small ⟨next, hn⟩
    simpa only [stageObservationMean, dite_eq_left hn] using stageDrift
  rw [expectedObservationBill_eq_sum_stageMeans input C hretained accounting budget]
  exact referenceFailureMass_sum_le_initial
    (stageObservationMean input C accounting budget)
    (fun next => ∫⁻ sample, entryEnvelopePotential input C accounting budget next sample
      ∂input.seededWorldLaw (Measure.dirac ()))
    I.stageCount (observationEnvelope input 0 ∅ (budget / 2)) drift
    (expected_entryEnvelopePotential_initial input C accounting budget).le

end PDROC.RetainedEnvelopeRun
