module

public import RootPaper_Prep_Account007

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open PaperProofs.Common.Native.RationalControllerComputation

namespace RootPaper.Prep

/-- An ordinary consumer jointly instantiates the original numerical
outputs, whole charged execution, and the already-closed scalar widths.
There is no supplied exponent/quota/output or complexity certificate. -/
theorem ordinary_original_preparation :
    ∃ coefficient degree : Nat, 0 < coefficient ∧ 0 < degree ∧
      ∀ (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget : Rat) (positive : 0 < budget),
        let calculation := preparationCalculation input C budget positive
        calculation.value.exponent = computedExponent (I:=I) budget ∧
        calculation.value.rows = originalRows input budget ∧
        calculation.value.qualification = numericQualification input C budget ∧
        calculation.operations.length ≤ 1000000*(arithmeticScale input C budget)^4 ∧
        (∀ op ∈ calculation.operations,op.Realized ∧ op.width ≤ 4096*arithmeticScale input C budget) ∧
        runningCost (inputSize input C budget) calculation ≤ coefficient*(arithmeticScale input C budget)^degree := by
  obtain ⟨c,d,hc,hd,actual⟩ := paper_preparation_accounted
  refine ⟨c,d,hc,hd,?_⟩
  intro I input C budget positive
  have run := actual I input C budget positive
  have bounds := original_preparationOps_bounded I input C budget positive
  rw [←run.2.1] at bounds
  refine ⟨congrArg NumericalPreparation.exponent run.1,congrArg NumericalPreparation.rows run.1,
    congrArg NumericalPreparation.qualification run.1,bounds.1,?_,run.2.2.2⟩
  intro op member
  exact ⟨run.2.2.1 op member,bounds.2 op member⟩

end RootPaper.Prep

#print axioms RootPaper.Prep.ordinary_original_preparation
