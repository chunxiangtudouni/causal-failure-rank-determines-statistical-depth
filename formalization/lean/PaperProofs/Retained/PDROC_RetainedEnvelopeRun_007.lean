module

public import PaperProofs.Retained.PDROC_RetainedEnvelopeRun_006
public import PaperProofs.Retained.PDROC_RetainedEnvelopeRun_EntryPartition_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics
open MeasureTheory
open scoped ENNReal

namespace PDROC.RetainedEnvelopeRun

variable {I : Instance}

theorem lintegral_potential_eq_tsum_entry (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage) :
    (∫⁻ sample, entryEnvelopePotential input C accounting budget stage.val sample
      ∂input.seededWorldLaw (Measure.dirac ())) =
      ∑' history : List (VisibleEvent I), ∫⁻ sample in stageEntryEvent input C accounting budget stage history,
        entryEnvelopePotential input C accounting budget stage.val sample
        ∂input.seededWorldLaw (Measure.dirac ()) := by
  exact EntryPartition.lintegral_eq_tsum_entry input C .uncapped accounting
    (idealPolicy input C hretained accounting budget) stage _
    (measurable_entryEnvelopePotential input C accounting budget stage.val)
    (fun sample absent => entryEnvelopePotential_zero_of_no_entry input C accounting budget stage sample absent)

theorem lintegral_nextPotential_eq_tsum_entry (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage) :
    (∫⁻ sample, entryEnvelopePotential input C accounting budget (stage.val + 1) sample
      ∂input.seededWorldLaw (Measure.dirac ())) =
      ∑' history : List (VisibleEvent I), ∫⁻ sample in stageEntryEvent input C accounting budget stage history,
        entryEnvelopePotential input C accounting budget (stage.val + 1) sample
        ∂input.seededWorldLaw (Measure.dirac ()) := by
  exact EntryPartition.lintegral_eq_tsum_entry input C .uncapped accounting
    (idealPolicy input C hretained accounting budget) stage _
    (measurable_entryEnvelopePotential input C accounting budget (stage.val + 1))
    (fun sample absent => nextPotential_zero_of_no_entry input C hretained accounting budget stage sample absent)

/-- Integrating the genuine full-history atom inequalities yields one
positive stage drift for the original retained execution. -/
theorem stageEnvelope_drift (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2) (stage : I.Stage) :
    (∫⁻ sample, runStageObservationBill input C .uncapped accounting (retainedRule input budget none) stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) +
    (∫⁻ sample, entryEnvelopePotential input C accounting budget (stage.val + 1) sample
      ∂input.seededWorldLaw (Measure.dirac ())) ≤
    (∫⁻ sample, entryEnvelopePotential input C accounting budget stage.val sample
      ∂input.seededWorldLaw (Measure.dirac ())) := by
  rw [lintegral_stageBill_eq_tsum_entry input C hretained accounting budget positive small stage,
    lintegral_nextPotential_eq_tsum_entry input C hretained accounting budget stage,
    lintegral_potential_eq_tsum_entry input C hretained accounting budget stage,
    ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum (stageEnvelope_drift_on_entry input C hretained accounting budget positive small stage)

end PDROC.RetainedEnvelopeRun
