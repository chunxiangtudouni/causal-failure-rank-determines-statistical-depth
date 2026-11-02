module

public import PaperProofs.Retained.PRet_RiskMassFlow_AtomMass_013

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory
open scoped ENNReal

namespace PRetRiskMassFlow

variable {I : Instance}

theorem stage_budget_mass_nonincreasing (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2) (stage : I.Stage) :
    input.seededWorldLaw (Measure.dirac ()) (fatal input C accounting budget stage) +
      (∫⁻ sample, nextBudgetPotential input C accounting budget stage sample ∂input.seededWorldLaw (Measure.dirac ())) ≤
      ∫⁻ sample, entryBudgetPotential input C accounting budget stage sample ∂input.seededWorldLaw (Measure.dirac ()) := by
  have next := lintegral_eq_tsum_entry input C accounting budget stage _
    (measurable_nextBudgetPotential input C accounting budget stage)
    (nextBudget_zero_of_no_entry input C hretained accounting budget positive small stage)
  calc
    _ = (∑' history : List (VisibleEvent I),input.seededWorldLaw (Measure.dirac ())
        (fatal input C accounting budget stage ∩ entryEvent input C accounting budget stage history)) +
        (∑' history : List (VisibleEvent I),∫⁻ sample in entryEvent input C accounting budget stage history,
          nextBudgetPotential input C accounting budget stage sample ∂input.seededWorldLaw (Measure.dirac ())) := by
      rw [fatalMass_eq_tsum_entry input C accounting budget stage,next]
    _ = ∑' history : List (VisibleEvent I),
        (input.seededWorldLaw (Measure.dirac ()) (fatal input C accounting budget stage ∩ entryEvent input C accounting budget stage history) +
          ∫⁻ sample in entryEvent input C accounting budget stage history,
            nextBudgetPotential input C accounting budget stage sample ∂input.seededWorldLaw (Measure.dirac ())) := ENNReal.tsum_add.symm
    _ ≤ ∑' history : List (VisibleEvent I),ENNReal.ofReal ((entryRisk I budget stage history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (entryEvent input C accounting budget stage history) :=
      ENNReal.tsum_le_tsum (budgetMass_on_entry_allStages input C hretained accounting budget positive small stage)
    _ = _ := (currentBudgetMass_eq_tsum_entry input C accounting budget stage).symm

noncomputable def budgetMassAt (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (next : ℕ) : ℝ≥0∞ :=
  if h : next < I.stageCount then ∫⁻ sample, entryBudgetPotential input C accounting budget ⟨next,h⟩ sample
    ∂input.seededWorldLaw (Measure.dirac ()) else 0

noncomputable def failureMassAt (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (next : ℕ) : ℝ≥0∞ :=
  if h : next < I.stageCount then input.seededWorldLaw (Measure.dirac ()) (fatal input C accounting budget ⟨next,h⟩) else 0

theorem budgetMassAt_step (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (next : ℕ) (bound : next < I.stageCount) :
    failureMassAt input C accounting budget next + budgetMassAt input C accounting budget (next+1) ≤
      budgetMassAt input C accounting budget next := by
  have successor : budgetMassAt input C accounting budget (next+1) =
      ∫⁻ sample, nextBudgetPotential input C accounting budget ⟨next,bound⟩ sample ∂input.seededWorldLaw (Measure.dirac ()) := by
    by_cases existsNext : next+1 < I.stageCount <;>
      simp only [budgetMassAt,nextBudgetPotential,existsNext,↓reduceDIte,lintegral_zero]
  rw [successor]
  simp only [failureMassAt,budgetMassAt,bound,dite_true]
  exact stage_budget_mass_nonincreasing input C hretained accounting budget positive small ⟨next,bound⟩

theorem budgetMassAt_terminal (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I) (budget : ℚ) :
    budgetMassAt input C accounting budget I.stageCount = 0 := by
  simp only [budgetMassAt,lt_self_iff_false,dite_false]

theorem budgetMassAt_initial (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I) (budget : ℚ) :
    budgetMassAt input C accounting budget 0 ≤ ENNReal.ofReal ((budget/2 : ℚ) : ℝ) := by
  by_cases nonzero : 0 < I.stageCount
  · simp only [budgetMassAt,nonzero,dite_true]
    have point : ∀ sample : Unit × input.World,entryBudgetPotential input C accounting budget ⟨0,nonzero⟩ sample =
        ENNReal.ofReal ((budget/2 : ℚ) : ℝ) := by
      intro sample
      have entered := entryHistory_stageZero input C .uncapped accounting (retainedRule input budget none) ⟨0,nonzero⟩ rfl sample
      have initialRisk : entryRisk I budget ⟨0,nonzero⟩ [] = some (budget/2) := rfl
      simp only [entryBudgetPotential,entered,initialRisk,Option.getD_some]
    calc
      _ = ∫⁻ _sample : Unit × input.World,ENNReal.ofReal ((budget/2 : ℚ) : ℝ) ∂input.seededWorldLaw (Measure.dirac ()) := lintegral_congr point
      _ ≤ _ := by simp
  · simp only [budgetMassAt,nonzero,dite_false]
    exact zero_le

/-- The full actual retained fatal-branch mass is bounded by the original
budget/2. This positive ENNReal telescope does not assume finite costs/time. -/
theorem fatalMass_sum_le_half (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2) :
    (∑ stage : I.Stage,input.seededWorldLaw (Measure.dirac ()) (fatal input C accounting budget stage)) ≤
      ENNReal.ofReal ((budget : ℝ)/2) := by
  have sumEq : (∑ stage : I.Stage,input.seededWorldLaw (Measure.dirac ()) (fatal input C accounting budget stage)) =
      ∑ next ∈ Finset.range I.stageCount,failureMassAt input C accounting budget next := by
    calc
      _ = ∑ stage : I.Stage,failureMassAt input C accounting budget stage.val := by
        apply Finset.sum_congr rfl
        intro stage _member
        unfold failureMassAt
        rw [dite_eq_left (show stage.val < I.stageCount from stage.isLt)]
      _ = _ := Fin.sum_univ_eq_sum_range _ I.stageCount
  rw [sumEq]
  calc
    _ ≤ ENNReal.ofReal ((budget/2 : ℚ) : ℝ) := referenceFailureMass_sum_le_initial
      (failureMassAt input C accounting budget) (budgetMassAt input C accounting budget) I.stageCount _
      (budgetMassAt_step input C hretained accounting budget positive small)
      (budgetMassAt_initial input C accounting budget)
    _ = _ := by congr 1; push_cast; rfl

end PRetRiskMassFlow
