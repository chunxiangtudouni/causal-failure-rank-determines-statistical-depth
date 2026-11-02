module

public import RootPaper_Reference_Ordinary024
public import RootPaper_Prep_Ordinary008

/-! Complete B23 at the paper's algorithmic layer. The concrete preparation
and measured controller produce the original native policy's actions.
The same all-path cost includes preparation exactly once and covers its
original stopping horizon. All constants and the strong WORD code precede
all instances. The preserved stronger Bool-machine specification is intact. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open MeasureTheory
open scoped ENNReal

namespace RootPaper.B23

open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RationalControllerComputation
open RootPaper.Reference.Charged

variable {I : Instance}

/-- Includes false numeric checks, with no qualification or precomputed
answer supplied to the preparation algorithm. -/
def PreparationPaperClaims : Prop :=
  ∃ coefficient degree : Nat, 0 < coefficient ∧ 0 < degree ∧
    ∀ (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget : Rat) (positive : 0 < budget),
      let calculation := RootPaper.Prep.preparationCalculation input C budget positive
      calculation.value.exponent = computedExponent (I := I) budget ∧
      calculation.value.rows = RootPaper.Prep.originalRows input budget ∧
      calculation.value.qualification = numericQualification input C budget ∧
      calculation.operations.length ≤ 1000000 * (arithmeticScale input C budget) ^ 4 ∧
      (∀ op ∈ calculation.operations, op.Realized ∧ op.width ≤ 4096 * arithmeticScale input C budget) ∧
      RootPaper.Prep.runningCost (inputSize input C budget) calculation ≤
        coefficient * (arithmeticScale input C budget) ^ degree

/-- A single concrete native run, its actual initialized controller,
original resource certificate and all-path computation cost. -/
def ExecutedReference (runtime : WordRuntime) (input : StatisticalInput I)
    (C : Contract I) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : Rat) (positive : 0 < budget) (exponent : Nat)
    (policy : Policy input C .native accounting Unit) : Prop :=
  Core input C accounting available budget exponent policy ∧
    (prepareOnce input C available budget positive).1.value = qualifiedResources input exponent ∧
    (∀ sample clock,
      ((prepareOnce input C available budget positive).2
        (run input C .native accounting policy.rule sample clock).history).action =
        policy.rule sample.1 (run input C .native accounting policy.rule sample clock).history) ∧
    (∀ sample, (run input C .native accounting policy.rule sample
      (originalHorizon input budget)).halted = true) ∧
    ∀ sample, totalRunningCost runtime input C accounting policy available budget positive sample ≤
      generalStructureFactor I * globalRate runtime *
        (arithmeticScale input C budget) ^ globalDegree runtime

def NativePaperClaims (runtime : WordRuntime) : Prop :=
  ∀ (I : Instance) (input : StatisticalInput I) (C : Contract I) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (delta : Real)
    (budget : Rat) (exponent : Nat) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : ReferenceCompleteOriginalQualification input C current.1 accounting available budget exponent),
    ExecutedReference runtime input C accounting available budget choice.positive exponent
      (GeneralNormalFees.completeNativeReferencePolicy input C current.1 accounting
        available budget exponent qualification)

/-- Risk and the full expected bill concern the same executed policy and
the original full starting tool set. No success conditioning is added. -/
def StatisticalPaperClaims (runtime : WordRuntime) : Prop :=
  ∀ (I : Instance) (input : StatisticalInput I) (C : Contract I) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (delta : Real), 0 < delta → delta ≤ 1 / 2 →
    ∀ (budget : Rat) (exponent : Nat) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : ReferenceCompleteOriginalQualification input C current.1 accounting I.tools budget exponent),
    let policy := GeneralNormalFees.completeNativeReferencePolicy input C current.1 accounting
      I.tools budget exponent qualification
    ExecutedReference runtime input C accounting I.tools budget choice.positive exponent policy ∧
      risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta ∧
      expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
        expectedBill input C .uncapped accounting
          (referenceIdealPolicy input C current.1 accounting I.tools budget).rule (Measure.dirac ())

/-- Complete paper claim with an actual fixed WORD implementation and
uniform positive constants, not caller-supplied implementation premises. -/
def FullPaperClaims : Prop :=
  PreparationPaperClaims ∧
    ∃ runtime : WordRuntime, 0 < globalRate runtime ∧ 0 < globalDegree runtime ∧
      NativePaperClaims runtime ∧ StatisticalPaperClaims runtime

theorem original_horizon_eq (input : StatisticalInput I) (budget : Rat) (exponent : Nat)
    (sameExponent : computedExponent (I := I) budget = exponent) :
    originalHorizon input budget = quotaActionBound I (referenceQuota input exponent) + 1 := by
  unfold originalHorizon computedQuotas
  rw [sameExponent]

theorem native_paper_claims (runtime : WordRuntime) : NativePaperClaims runtime := by
  intro I input C current accounting available delta budget exponent choice qualification
  obtain ⟨core, actions, cost⟩ := ordinary_native_reference runtime input C current accounting
    available delta budget exponent choice qualification
  refine ⟨core, ?_, actions, ?_, cost⟩
  · rw [initialize_value, original_rows, core.exponent_eq, core.numeric_check]
    rfl
  · intro sample
    rw [original_horizon_eq input budget exponent core.exponent_eq]
    exact core.halted sample

theorem statistical_paper_claims (runtime : WordRuntime) : StatisticalPaperClaims runtime := by
  intro I input C current accounting delta positive small budget exponent choice qualification
  obtain ⟨_, safe, bill⟩ := statistical_core input C current accounting delta positive small
    budget exponent choice qualification
  exact ⟨native_paper_claims runtime I input C current accounting I.tools delta budget exponent
    choice qualification, safe, bill⟩

theorem full_paper_claims : FullPaperClaims := by
  obtain ⟨runtime⟩ := wordRuntime_exists
  exact ⟨RootPaper.Prep.ordinary_original_preparation, runtime,
    globalRate_positive runtime, globalDegree_positive runtime,
    native_paper_claims runtime, statistical_paper_claims runtime⟩

#print axioms RootPaper.B23.full_paper_claims

end RootPaper.B23
