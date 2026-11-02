module

public import PaperProofs.Statistics.PDROC_ExactAttainment_001
public import PaperProofs.Statistics.PDROC_Integral_001
public import PaperProofs.Statistics.PDROC_Lower_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Statistics.PDROC

open BinarySymmetric BinarySymmetric.Parameters

universe u

/-- The original D05 lower bound, including every private seed universe,
arbitrary non-MAP decisions, and infinite observation-fee comparators. -/
theorem rocArbitraryDecisionLower (P : Parameters) : RocArbitraryDecisionLower.{u} P := by
  intro Seed ms ν hν test he heone
  let : MeasurableSpace Seed := ms
  let : IsProbabilityMeasure ν := hν
  by_cases htop : P.experiment.bayesObservationCharge ν test = ⊤
  · rw [htop]
    exact le_top
  · have hobj : P.experiment.bayesObjective ν test 0 ≠ ⊤ := by
      simpa only [BinaryExperiment.bayesObjective, zero_mul, add_zero] using htop
    have hf := P.experiment.bayesObjective_finite_expectedSamples ν test 0 hobj
    have hp : 0 < P.adjustedBayesError ν test := lt_min he (by linarith)
    exact _root_.PDROC.rocPrice_le_charge_of_posterior_average P ν test hf
      (_root_.PDROC.posteriorError_integrable P ν test)
      (P.adjustedBayesError ν test) hp (P.adjustedBayesError_mem_Icc ν test).2
      (_root_.PDROC.integral_posteriorError_le_adjusted P ν test hf)

/-- Full original ExactROCClaims: no performance is assumed in the comparator
or in the rule structure, and no finite-ET hypothesis is added. -/
theorem exactROCClaims (P : Parameters) : ExactROCClaims.{u} P :=
  ⟨rocArbitraryDecisionLower P, rocMAPAttains P, rocArbitraryDecisionAttains P⟩

end PaperProofs.Statistics.PDROC
