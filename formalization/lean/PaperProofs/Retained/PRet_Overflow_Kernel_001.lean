module

public import PaperProofs.Retained.PRet_RiskMassFlow_Realization_005
public import PaperProofs.Retained.PRet_RiskMassFlow_Floor_007
public import PaperProofs.Retained.PRet_Truncation_120
public import PaperProofs.Common.ReferenceCertification

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory
open scoped ENNReal

namespace PRetOverflow

variable {I : Instance}

def entryChoice (I : Instance) (budget : ℚ) (stage : I.Stage) : Unit × List (VisibleEvent I) → Option ℚ :=
  fun record => PRetRiskMassFlow.entryTarget I budget stage record.2

theorem measurable_entryChoice (budget : ℚ) (stage : I.Stage) : Measurable (entryChoice I budget stage) :=
  measurable_of_countable _

theorem entryChoice_floor (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (stage : I.Stage) (history : List (VisibleEvent I)) (p : ℚ)
    (target : PRetRiskMassFlow.entryTarget I budget stage history = some p) :
    budget / referenceQuotaConstant I.stageCount ≤ p := by
  have localFloor := PRetRiskMassFlow.entryTarget_floor budget positive small stage history p target
  have stageBound := stage.isLt
  change stage.val < I.stageCount at stageBound
  have powers : (2:ℚ)^(stage.val+1) ≤ (2:ℚ)^(I.stageCount+1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have comparison : budget/(2:ℚ)^(I.stageCount+1) ≤ budget/(2:ℚ)^(stage.val+1) :=
    div_le_div_of_nonneg_left positive.le (by positivity) powers
  calc
    budget / referenceQuotaConstant I.stageCount = (budget/(2:ℚ)^(I.stageCount+1))/6 := by
      unfold referenceQuotaConstant
      ring
    _ ≤ (budget/(2:ℚ)^(stage.val+1))/6 := div_le_div_of_nonneg_right comparison (by norm_num)
    _ ≤ p := localFloor

theorem retainedOverflow_subset_entryOverflow (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I) (budget : ℚ)
    (positive : 0 < budget) (small : budget ≤ 1/2) (quota : I.Stage → ℕ) :
    PRetTruncation120.retainedOverflow input C hretained accounting budget quota ⊆
      ⋃ stage : I.Stage, entryPosteriorOverflow input C .uncapped accounting
        (idealPolicy input C hretained accounting budget).rule stage (entryChoice I budget stage) (quota stage) := by
  rintro ⟨⟨⟩,world⟩ ⟨n,stage,active,selected,exceeded⟩
  apply Set.mem_iUnion.mpr
  refine ⟨stage,?_⟩
  obtain ⟨m,_bound,path⟩ := run_has_prefix input C .uncapped accounting
    (idealPolicy input C hretained accounting budget).rule
    (idealPolicy input C hretained accounting budget).legal ((),world) n
  obtain ⟨history,p,entry,target,strict⟩ := PRetRiskMassFlow.prefix_review_realization input C hretained accounting
    budget positive small ((),world) path active stage selected
  change ∃ p : ℚ, entryGatedTarget (entryChoice I budget stage)
    (entrySeedHistory input C .uncapped accounting (idealPolicy input C hretained accounting budget).rule stage ((),world)) = some p ∧
      (quota stage : ℕ∞) < (input.experiment stage).posteriorThresholdStop p (world stage).2
  refine ⟨p,?_,lt_of_le_of_lt exceeded strict⟩
  apply (entryGatedTarget_some_iff (entryChoice I budget stage) _ p).mpr
  exact ⟨history,entry,target⟩

theorem stage_entryOverflow_le (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (delta : ℝ) (smallDelta : delta ≤ 1/2) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget) (positiveN : 0 < I.stageCount)
    (stage : I.Stage) :
    input.seededWorldLaw (Measure.dirac ())
      (entryPosteriorOverflow input C .uncapped accounting
        (idealPolicy input C hretained accounting budget).rule stage
        (entryChoice I budget stage) (referenceQuota input exponent stage)) ≤
      ENNReal.ofReal (delta/(2*I.stageCount)) := by
  have minimal := BinaryExperiment.quotaExponent_minimal budget choice.positive I.stageCount
  rw [choice.same_exponent] at minimal
  apply entryPosteriorOverflow_referenceRisk_le input C .uncapped accounting
    (idealPolicy input C hretained accounting budget) (Measure.dirac ()) stage
    (entryChoice I budget stage) (measurable_entryChoice budget stage)
    (fun _ history p target => PRetRiskMassFlow.entryTarget_valid budget stage history p target)
    delta smallDelta budget choice.positive choice.conservative I.stageCount positiveN exponent minimal.2.1
  intro _ history p target
  have floor := entryChoice_floor budget choice.positive choice.small stage history p target
  exact_mod_cast floor

end PRetOverflow
