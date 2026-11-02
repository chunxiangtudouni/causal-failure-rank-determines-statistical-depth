module

public import PaperProofs.Star.PStarLR_RealTestLaw_007
public import PaperProofs.Common.NativeHeadBayes
public import Mathlib.Probability.Independence.Integration

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarStageProduct011

open Common Common.Native MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {I : Instance}

/-- Finite products of genuine stage-localSample random variables factor on the
original hidden world; this follows from its proved independent stage law. -/
theorem lintegral_stageProduct (input : StatisticalInput I) (stages : Finset I.Stage)
    (f : ∀ stage, input.StageSample stage → ℝ≥0∞) (measurable : ∀ stage, Measurable (f stage)) :
    (∫⁻ world : input.World, ∏ stage ∈ stages, f stage (world stage) ∂input.worldLaw) =
      ∏ stage ∈ stages, ∫⁻ localSample, f stage localSample ∂input.stageLaw stage := by
  have independent := input.worldLaw_independent_stages.comp f measurable
  calc
    _ = ∏ stage ∈ stages, ∫⁻ world : input.World, f stage (world stage) ∂input.worldLaw :=
      lintegral_prod_eq_prod_lintegral_of_indepFun (μ := input.worldLaw) stages
        (fun (stage : I.Stage) (world : input.World) => f stage (world stage)) independent
        (fun stage => (measurable stage).comp (measurable_pi_apply stage))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro stage _member
      rw [← lintegral_map (measurable stage) (measurable_pi_apply stage), input.worldLaw_coordinate]

theorem lintegral_stageProduct_le (input : StatisticalInput I) (stages : Finset I.Stage)
    (f : ∀ stage, input.StageSample stage → ℝ≥0∞) (measurable : ∀ stage, Measurable (f stage))
    (bound : I.Stage → ℝ≥0∞)
    (bounded : ∀ stage ∈ stages, (∫⁻ localSample, f stage localSample ∂input.stageLaw stage) ≤ bound stage) :
    (∫⁻ world : input.World, ∏ stage ∈ stages, f stage (world stage) ∂input.worldLaw) ≤
      ∏ stage ∈ stages, bound stage := by
  rw [lintegral_stageProduct input stages f measurable]
  exact Finset.prod_le_prod bounded

/-- Gate-weighted real localSample charge. The current stage is excluded from
the past-error gate, so its true observation bill retains its original law. -/
theorem lintegral_stageProduct_charge (input : StatisticalInput I) (past : Finset I.Stage)
    (stage : I.Stage) (fresh : stage ∉ past)
    (f : ∀ earlier, input.StageSample earlier → ℝ≥0∞) (measurable : ∀ earlier, Measurable (f earlier))
    (charge : input.StageSample stage → ℝ≥0∞) (measurableCharge : Measurable charge) :
    (∫⁻ world : input.World, (∏ earlier ∈ past, f earlier (world earlier)) * charge (world stage)
      ∂input.worldLaw) =
      (∏ earlier ∈ past, ∫⁻ localSample, f earlier localSample ∂input.stageLaw earlier) *
        ∫⁻ localSample, charge localSample ∂input.stageLaw stage := by
  classical
  let selected : ∀ earlier, input.StageSample earlier → ℝ≥0∞ := fun earlier =>
    if equal : earlier = stage then fun localSample => charge (equal ▸ localSample) else f earlier
  have selectedMeasurable : ∀ earlier, Measurable (selected earlier) := by
    intro earlier
    by_cases equal : earlier = stage
    · subst earlier
      simpa only [selected, ↓reduceDIte] using measurableCharge
    · simpa only [selected, equal, ↓reduceDIte] using measurable earlier
  have product := lintegral_stageProduct input (insert stage past) selected selectedMeasurable
  have earlierSelected (earlier : I.Stage) (member : earlier ∈ past) : selected earlier = f earlier := by
    have unequal : earlier ≠ stage := by intro equal; subst earlier; exact fresh member
    simp only [selected, unequal, ↓reduceDIte]
  simp only [Finset.prod_insert fresh, selected, ↓reduceDIte] at product
  have leftProduct : (fun world : input.World =>
      charge (world stage) * ∏ earlier ∈ past, selected earlier (world earlier)) =
      (fun world => (∏ earlier ∈ past, f earlier (world earlier)) * charge (world stage)) := by
    funext world
    rw [Finset.prod_congr rfl (fun earlier member => congrFun (earlierSelected earlier member) (world earlier)), mul_comm]
  have rightProduct : (∏ earlier ∈ past, ∫⁻ localSample, selected earlier localSample ∂input.stageLaw earlier) =
      ∏ earlier ∈ past, ∫⁻ localSample, f earlier localSample ∂input.stageLaw earlier := by
    apply Finset.prod_congr rfl
    intro earlier member
    rw [earlierSelected earlier member]
  change (∫⁻ world : input.World, charge (world stage) * ∏ earlier ∈ past, selected earlier (world earlier)
    ∂input.worldLaw) = (∫⁻ localSample, charge localSample ∂input.stageLaw stage) *
      ∏ earlier ∈ past, ∫⁻ localSample, selected earlier localSample ∂input.stageLaw earlier at product
  rw [leftProduct, rightProduct, mul_comm] at product
  exact product

end PaperProofs.Star.PStarStageProduct011

