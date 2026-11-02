module

public import PaperProofs.Common.PSTR_ST_TableDecision_005

/-! Original quota overflow for the actual table tie, on every initial
available set. This is the genuine exhausted-review event, not merely a
potential test event. Original exponent and caps are retained. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PaperProofs.Common.Native.PSTRStatistics.TableOverflow

open PaperProofs.Statistics PaperProofs.Structure.LaminarTree
open CompactPrice TableAlignment TableOrigin TableDecision

variable {I : Instance}

def tableOverflow (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ) : Set (Unit × input.World) :=
  ⋃ stage, tableStageOverflow input C hearly accounting available budget quota stage

theorem tableStageOverflow_subset_entryPosteriorOverflow (input : StatisticalInput I)
    (hlaminar : LaminarSchedule I.compatibility) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (quota : I.Stage → ℕ) (stage : I.Stage) :
    tableStageOverflow input C hearly accounting available budget quota stage ⊆
      entryPosteriorOverflow input C .uncapped accounting
        (tableIdealPolicy input C hearly accounting available budget).rule stage
        (tableEntryChoice input available budget) (quota stage) := by
  rintro ⟨⟨⟩, world⟩ ⟨n, hactive, hreview, hquota⟩
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting
    (tableIdealPolicy input C hearly accounting available budget).rule
    (tableIdealPolicy input C hearly accounting available budget).legal ((), world) n
  obtain ⟨history, p, hentry, htarget, hstrict⟩ := prefix_tableReview_realization input hlaminar C hearly
    accounting available budget hbudget hsmall ((), world) hp hactive stage hreview
  refine ⟨p, ?_, hquota.trans_lt hstrict⟩
  change entryGatedTarget (tableEntryChoice input available budget)
    ((), entryHistory input C .uncapped accounting (tableRule input available budget none) stage ((), world)) = some p
  rw [hentry]
  exact htarget

theorem table_entry_overflow_bound (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (delta : ℝ) (hsmall : delta ≤ 1 / 2) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (stage : I.Stage) :
    input.seededWorldLaw (Measure.dirac ())
      (entryPosteriorOverflow input C .uncapped accounting
        (tableIdealPolicy input C hearly accounting available budget).rule stage
        (tableEntryChoice input available budget) (referenceQuota input exponent stage)) ≤
          ENNReal.ofReal (delta / (2 * I.stageCount)) := by
  have hminimal := BinaryExperiment.quotaExponent_minimal budget choice.positive I.stageCount
  rw [choice.same_exponent] at hminimal
  have hN : 0 < I.stageCount := by
    have hs : stage.val < I.stageCount := stage.isLt
    omega
  apply entryPosteriorOverflow_referenceRisk_le input C .uncapped accounting
    (tableIdealPolicy input C hearly accounting available budget) (Measure.dirac ()) stage
    (tableEntryChoice input available budget) (measurable_tableEntryChoice input available budget)
    (fun _ history p hp => (tableEntryTarget_bounds input available budget p choice.positive choice.small history hp).imp_right And.left)
    delta hsmall budget choice.positive choice.conservative I.stageCount hN exponent hminimal.2.1
  intro _ history p hp
  have hf := (tableEntryTarget_bounds input available budget p choice.positive choice.small history hp).2.2
  exact_mod_cast hf

theorem tableOverflowGuarantee (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (delta : ℝ) (hsmall : delta ≤ 1 / 2) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget) :
    input.seededWorldLaw (Measure.dirac ())
      (tableOverflow input C hearly accounting available budget (referenceQuota input exponent)) ≤
        ENNReal.ofReal (delta / 2) := by
  unfold tableOverflow
  by_cases hN : 0 < I.stageCount
  · calc
      _ ≤ ∑ stage : I.Stage, input.seededWorldLaw (Measure.dirac ())
          (tableStageOverflow input C hearly accounting available budget (referenceQuota input exponent) stage) :=
        measure_iUnion_fintype_le _ _
      _ ≤ ∑ _stage : I.Stage, ENNReal.ofReal (delta / (2 * I.stageCount)) := by
        apply Finset.sum_le_sum
        intro stage _
        exact (measure_mono (tableStageOverflow_subset_entryPosteriorOverflow input hlaminar C hearly accounting
          available budget choice.positive choice.small (referenceQuota input exponent) stage)).trans
            (table_entry_overflow_bound input C hearly accounting available delta hsmall exponent budget choice stage)
      _ = ENNReal.ofReal (delta / 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Instance.Stage, Fintype.card_fin, nsmul_eq_mul]
        change (I.stageCount : ℝ≥0∞) * ENNReal.ofReal (delta / (2 * I.stageCount)) = _
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg I.stageCount)]
        congr 1
        have hNR : (I.stageCount : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        field_simp [hNR]
  · have : IsEmpty I.Stage := ⟨fun stage => by
      have hs : stage.val < I.stageCount := stage.isLt
      omega⟩
    simp

end PaperProofs.Common.Native.PSTRStatistics.TableOverflow
