module

public import RootPaper_B23_Core001
public import RootPaper_Prep_Account007
import Lean.Util.CollectAxioms

/-! The actual charged preparation feeds the SAME original native policy.
The original quota/cap test succeeds under its original qualification; H0
remains that qualification, not a computed numeric fact. No whole-controller
cost theorem is claimed before the separately assigned controller work. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootPaper.B23

open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RationalControllerComputation

variable {I : Instance}

/-- Expected ORIGINAL numerical resources. This is a specification, not
supplied runtime data or fuel for the preparation algorithm. -/
def qualifiedResources (input : StatisticalInput I) (exponent : Nat) : RootPaper.Prep.NumericalPreparation I :=
  ⟨exponent, (List.finRange I.stageCount).map (fun stage =>
    (stage, ⟨(input.experiment stage).channelDriftLower,
      (input.experiment stage).channelIntegerMax, (input.experiment stage).priorIntegerMax,
      referenceQuota input exponent stage⟩)), true⟩

theorem original_rows (input : StatisticalInput I) (budget : Rat) :
    RootPaper.Prep.originalRows input budget =
      (qualifiedResources input (computedExponent (I := I) budget)).rows := by
  simp only [RootPaper.Prep.originalRows, RootPaper.Prep.prepareStage_eq, qualifiedResources]
  rfl

/-- One uniform charged preparation, original results and same-policy
native resources. The scalar cost includes the SAME recursive value/log
and its actual control, input-access and record construction accounting. -/
theorem prepared_native :
    ∃ coefficient degree : Nat, 0 < coefficient ∧ 0 < degree ∧
      ∀ (I : Instance) (input : StatisticalInput I) (C : Contract I) (current : C.IsCurrentAllocation)
        (accounting : NormalAccounting I) (available : Finset I.Tool) (delta : Real)
        (budget : Rat) (exponent : Nat) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
        (qualification : ReferenceCompleteOriginalQualification input C current.1 accounting available budget exponent),
        let calculation := RootPaper.Prep.preparationCalculation input C budget choice.positive
        let policy := GeneralNormalFees.completeNativeReferencePolicy input C current.1 accounting available budget exponent qualification
        calculation.value = qualifiedResources input exponent ∧
          calculation.operations = RootPaper.Prep.preparationOps input C budget choice.positive ∧
          (∀ op ∈ calculation.operations, op.Realized) ∧
          RootPaper.Prep.runningCost (inputSize input C budget) calculation ≤
            coefficient * (arithmeticScale input C budget)^degree ∧
          Core input C accounting available budget exponent policy := by
  obtain ⟨coefficient, degree, coefficientPositive, degreePositive, prepare⟩ :=
    RootPaper.Prep.paper_preparation_accounted
  refine ⟨coefficient, degree, coefficientPositive, degreePositive, ?_⟩
  intro I input C current accounting available delta budget exponent choice qualification
  have resources := core input C current accounting available delta budget exponent choice qualification
  obtain ⟨value, operations, realized, cost⟩ := prepare I input C budget choice.positive
  refine ⟨?_, operations, realized, cost, resources⟩
  rw [value, original_rows, resources.exponent_eq, resources.numeric_check]
  rfl

end RootPaper.B23

#print axioms RootPaper.B23.prepared_native

open Lean Elab Command
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`RootPaper.B23.qualifiedResources, `RootPaper.B23.original_rows,
      `RootPaper.B23.prepared_native, `RootPaper.Prep.paper_preparation_accounted] do
    for ax in ← collectAxioms name do
      unless allowed.contains ax do throwError m!"ROOT_PAPER_PREP_NATIVE_STD3_FAIL forbidden={ax} declaration={name}"
  logInfo "ROOT_PAPER_PREP_NATIVE_STD3_PASS endpoints=4 forbidden=0"
