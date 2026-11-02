module

public import PaperProofs.Retained.PRet_Overflow_Kernel_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory
open scoped ENNReal

namespace PRetOverflow

variable {I : Instance}

theorem retainedOverflow_le_half (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (delta : ℝ) (_positiveDelta : 0 < delta) (smallDelta : delta ≤ 1/2) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget) :
    input.seededWorldLaw (Measure.dirac ())
      (PRetTruncation120.retainedOverflow input C hretained accounting budget (referenceQuota input exponent)) ≤
      ENNReal.ofReal (delta/2) := by
  refine (measure_mono (retainedOverflow_subset_entryOverflow input C hretained accounting budget
    choice.positive choice.small (referenceQuota input exponent))).trans ?_
  by_cases positiveN : 0 < I.stageCount
  · calc
      _ ≤ ∑ stage : I.Stage, input.seededWorldLaw (Measure.dirac ())
          (entryPosteriorOverflow input C .uncapped accounting
            (idealPolicy input C hretained accounting budget).rule stage
            (entryChoice I budget stage) (referenceQuota input exponent stage)) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _stage : I.Stage, ENNReal.ofReal (delta/(2*I.stageCount)) := by
        apply Finset.sum_le_sum
        intro stage _
        exact stage_entryOverflow_le input C hretained accounting delta smallDelta exponent budget choice positiveN stage
      _ = ENNReal.ofReal (delta/2) := by
        simp only [Finset.sum_const,Finset.card_univ,Instance.Stage,Fintype.card_fin,nsmul_eq_mul]
        change (I.stageCount : ℝ≥0∞)*ENNReal.ofReal (delta/(2*I.stageCount)) = _
        rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg I.stageCount)]
        congr 1
        have nonzero : (I.stageCount : ℝ) ≠ 0 := by exact_mod_cast positiveN.ne'
        field_simp [nonzero]
  · have : IsEmpty I.Stage := ⟨fun stage => by have bound := stage.isLt; change stage.val < I.stageCount at bound; omega⟩
    simp

end PRetOverflow
