module

public import PaperProofs.Retained.PRet_RiskMassFlow_ChildEnvelope_012

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory
open scoped ENNReal

namespace PRetRiskMassFlow

variable {I : Instance}

theorem budgetMass_on_entry (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (stage nextStage : I.Stage) (successor : nextStage.val = stage.val+1) (history : List (VisibleEvent I)) :
    input.seededWorldLaw (Measure.dirac ()) (fatal input C accounting budget stage ∩ entryEvent input C accounting budget stage history) +
      (∫⁻ sample in entryEvent input C accounting budget stage history,
        entryBudgetPotential input C accounting budget nextStage sample ∂input.seededWorldLaw (Measure.dirac ())) ≤
      ENNReal.ofReal ((entryRisk I budget stage history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (entryEvent input C accounting budget stage history) := by
  classical
  let μ := input.seededWorldLaw (Measure.dirac ())
  let E := entryEvent input C accounting budget stage history
  have hE : MeasurableSet E := measurableSet_entryEvent input C accounting budget stage history
  by_cases nonempty : ∃ sample : Unit × input.World, sample ∈ E
  · obtain ⟨witness,entered⟩ := nonempty
    obtain ⟨cache,kind,_replay,_healthy,valid,_query,riskEq,kindEq,targetEq⟩ :=
      entry_cache input C hretained accounting budget positive small stage witness history entered
    have integral : (∫⁻ sample in E, entryBudgetPotential input C accounting budget nextStage sample ∂μ) ≤
        ∫⁻ sample in E, childBudgetEnvelope input C accounting budget stage kind cache.risk sample ∂μ := by
      apply setLIntegral_mono' hE
      intro sample member
      exact nextEntryBudget_le_on_entry input C hretained accounting budget positive small stage nextStage successor
        history kind cache.risk kindEq riskEq sample member
    change μ (fatal input C accounting budget stage ∩ E) +
      (∫⁻ sample in E,entryBudgetPotential input C accounting budget nextStage sample ∂μ) ≤
        ENNReal.ofReal ((entryRisk I budget stage history).getD 0 : ℝ) * μ E
    rw [riskEq,Option.getD_some]
    cases kind with
    | infiniteRank =>
      have zero : μ (fatal input C accounting budget stage ∩ E) = 0 := by
        rw [show fatal input C accounting budget stage ∩ E = ∅ from
          fatal_entry_empty input C accounting budget stage history (by rw [kindEq]; simp)]
        exact measure_empty
      rw [zero,zero_add]
      simpa only [childBudgetEnvelope,setLIntegral_const] using integral
    | noTool =>
      have error : μ (writeError input C accounting budget stage ∩ E) ≤
          ENNReal.ofReal ((cache.risk/2 : ℚ) : ℝ) * μ E :=
        writeError_on_entry_le input C hretained accounting budget positive small stage history (cache.risk/2) targetEq
      have failed : μ (fatal input C accounting budget stage ∩ E) ≤ μ (writeError input C accounting budget stage ∩ E) :=
        measure_mono (fun _ member => ⟨member.1.1,member.2⟩)
      have child : (∫⁻ sample in E, entryBudgetPotential input C accounting budget nextStage sample ∂μ) ≤
          ENNReal.ofReal ((cache.risk/2 : ℚ) : ℝ) * μ E := by
        simpa only [childBudgetEnvelope,setLIntegral_const] using integral
      calc
        _ ≤ μ (writeError input C accounting budget stage ∩ E) + ENNReal.ofReal ((cache.risk/2 : ℚ) : ℝ) * μ E := add_le_add failed child
        _ = ENNReal.ofReal ((cache.risk/2 : ℚ) : ℝ) * μ E + μ (writeError input C accounting budget stage ∩ E) := add_comm _ _
        _ ≤ _ := referenceBudget_noTool_entry_mass cache.risk valid.1.le _ _ error
    | finiteBad depth =>
      have zero : μ (fatal input C accounting budget stage ∩ E) = 0 := by
        rw [show fatal input C accounting budget stage ∩ E = ∅ from
          fatal_entry_empty input C accounting budget stage history (by rw [kindEq]; simp)]
        exact measure_empty
      rw [zero,zero_add]
      have error : μ (writeError input C accounting budget stage ∩ E) ≤
          ENNReal.ofReal ((controllerTarget cache.risk depth.val : ℚ) : ℝ) * μ E :=
        writeError_on_entry_le input C hretained accounting budget positive small stage history _ targetEq
      have measurableError := measurableSet_writeError input C accounting budget stage
      have evaluate : (∫⁻ sample in E, childBudgetEnvelope input C accounting budget stage (.finiteBad depth) cache.risk sample ∂μ) =
          ENNReal.ofReal ((cache.risk/2 : ℚ) : ℝ) * μ E +
            ENNReal.ofReal ((controllerBadRisk cache.risk (controllerTarget cache.risk depth.val) : ℚ) : ℝ) *
              μ (writeError input C accounting budget stage ∩ E) := by
        simp only [childBudgetEnvelope]
        rw [lintegral_add_right _ (measurable_const.indicator measurableError),setLIntegral_const,
          lintegral_indicator measurableError,setLIntegral_const,Measure.restrict_apply measurableError]
      exact (integral.trans_eq evaluate).trans (referenceBudget_finiteBad_entry_mass cache.risk valid depth _ _ error)
  · have empty : E = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun sample member => nonempty ⟨sample,member⟩)
    change μ (fatal input C accounting budget stage ∩ E) +
      (∫⁻ sample in E, entryBudgetPotential input C accounting budget nextStage sample ∂μ) ≤ _
    rw [empty]
    simp

theorem fatalMass_on_entry_le (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (stage : I.Stage) (history : List (VisibleEvent I)) :
    input.seededWorldLaw (Measure.dirac ()) (fatal input C accounting budget stage ∩ entryEvent input C accounting budget stage history) ≤
      ENNReal.ofReal ((entryRisk I budget stage history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (entryEvent input C accounting budget stage history) := by
  classical
  let μ := input.seededWorldLaw (Measure.dirac ())
  let E := entryEvent input C accounting budget stage history
  by_cases nonempty : ∃ sample : Unit × input.World, sample ∈ E
  · obtain ⟨witness,entered⟩ := nonempty
    obtain ⟨cache,kind,_replay,_healthy,valid,_query,riskEq,kindEq,targetEq⟩ :=
      entry_cache input C hretained accounting budget positive small stage witness history entered
    change μ (fatal input C accounting budget stage ∩ E) ≤ ENNReal.ofReal ((entryRisk I budget stage history).getD 0 : ℝ) * μ E
    rw [riskEq,Option.getD_some]
    cases kind with
    | infiniteRank | finiteBad depth =>
      rw [show fatal input C accounting budget stage ∩ E = ∅ from
        fatal_entry_empty input C accounting budget stage history (by rw [kindEq]; simp),measure_empty]
      exact zero_le
    | noTool =>
      have error := writeError_on_entry_le input C hretained accounting budget positive small stage history (cache.risk/2) targetEq
      have subset : fatal input C accounting budget stage ∩ E ⊆ writeError input C accounting budget stage ∩ E :=
        fun _ member => ⟨member.1.1,member.2⟩
      have half : ((cache.risk/2 : ℚ) : ℝ) ≤ (cache.risk : ℝ) := by exact_mod_cast (by linarith [valid.1] : cache.risk/2 ≤ cache.risk)
      exact (measure_mono subset).trans (error.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal half) (μ E)))
  · have empty : E = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun sample member => nonempty ⟨sample,member⟩)
    change μ (fatal input C accounting budget stage ∩ E) ≤ _
    rw [empty]
    simp

theorem budgetMass_on_entry_allStages (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (stage : I.Stage) (history : List (VisibleEvent I)) :
    input.seededWorldLaw (Measure.dirac ()) (fatal input C accounting budget stage ∩ entryEvent input C accounting budget stage history) +
      (∫⁻ sample in entryEvent input C accounting budget stage history,
        nextBudgetPotential input C accounting budget stage sample ∂input.seededWorldLaw (Measure.dirac ())) ≤
      ENNReal.ofReal ((entryRisk I budget stage history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (entryEvent input C accounting budget stage history) := by
  by_cases next : stage.val+1 < I.stageCount
  · simpa only [nextBudgetPotential,next,↓reduceDIte] using
      budgetMass_on_entry input C hretained accounting budget positive small stage ⟨stage.val+1,next⟩ rfl history
  · simpa only [nextBudgetPotential,next,↓reduceDIte,lintegral_zero,add_zero] using
      fatalMass_on_entry_le input C hretained accounting budget positive small stage history

end PRetRiskMassFlow
