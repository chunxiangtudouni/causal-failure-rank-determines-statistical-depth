module

public import RootPaper_L01_HeadBound002
public import RootPaper_TableCost_Native017
public import RootPaper_Prep_Ordinary008

/-! Full paper-scope L01. This is distinct from the preserved stronger
Bool-machine FullClaims. Every implementation, count, arithmetic cost,
symbolic output and performance property below is a conclusion. Native
and sharp results share the very same policy and prepared heap. The
original infinite-rank result keeps its original hypotheses.

Structural work uses the already verified finite-word packing model;
statistical arithmetic, saved records and symbolic copies have the
explicit binary/linked-record costs supplied by the concrete algorithms.
No source-to-machine compiler or extra tape serializer is asserted. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open MeasureTheory
open scoped ENNReal

namespace RootPaper.L01

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open PaperProofs.Structure PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RationalControllerComputation

variable {I : Instance}

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

def ScalarPaperClaims : Prop :=
  (∀ operation : RootPaper.Prep.Operation, operation.Realized) ∧
  ∀ (I : Instance) (S D : Nat) (call : RootPaper.Reference.ScalarCall I),
    RootPaper.TableCost.CallBound S D call → RootPaper.TableCost.ScalarRealized call

def StructuralPaperClaims : Prop :=
  0 < RootPaper.Table.preprocessingConstant ∧
  ∀ (q : Nat) (full : List (Finset (Fin q))), LaminarSchedule full →
    treeSize q full ≤ full.length + q + 1 ∧
    ∀ used : Finset (Fin q), ∃ prepSteps headSteps,
      RootPaper.Table.PreparedRun full used prepSteps headSteps ∧
      (0 < full.length → 0 < q →
        callCost q full RootPaper.Table.heads .query headSteps
            (RootPaper.Table.preparedHeap full used prepSteps) ≤
          120000 * (full.length * q * treeSize q full))

def SymbolicPaperClaims : Prop :=
  ∀ (I : Instance) (input : StatisticalInput I), LaminarSchedule I.compatibility →
    ∀ available : Finset I.Tool, ∃ prepSteps headSteps,
      RootPaper.Table.PreparedRun I.compatibility (Finset.univ \ available) prepSteps headSteps ∧
      HeadResult input available prepSteps headSteps

def ChargedJointRun (runtime : RootPaper.TableCost.WordCode)
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : Rat) (positive : 0 < budget) (exponent : Nat)
    (policy : Policy input C .native accounting Unit) : Prop :=
  ∃ prepSteps headSteps,
    RootPaper.Table.PreparedRun I.compatibility (Finset.univ \ available) prepSteps headSteps ∧
    RootPaper.Table.NativeWordRun input C accounting available (referenceQuota input exponent) policy
      (RootPaper.Table.preparedHeap I.compatibility (Finset.univ \ available) prepSteps) ∧
    HeadResult input available prepSteps headSteps ∧
    RootPaper.TableCost.NativeChargeBound runtime
      (RootPaper.TableCost.nativeRate runtime) (RootPaper.TableCost.nativeDegree runtime)
      input C accounting available budget positive policy
      (RootPaper.Table.preparedHeap I.compatibility (Finset.univ \ available) prepSteps)

def NativePaperClaims (runtime : RootPaper.TableCost.WordCode) : Prop :=
  ∀ (I : Instance), LaminarSchedule I.compatibility →
    ∀ (input : StatisticalInput I) (C : Contract I), C.IsCurrentAllocation →
    ∀ (accounting : NormalAccounting I) (available : Finset I.Tool) (delta : Real),
      0 < delta → delta ≤ 1 / 2 → ∀ (budget : Rat) (exponent : Nat)
      (choice : ReferenceRiskChoice I.stageCount delta exponent budget),
      CompactPrice.OriginalQualification input C accounting available budget exponent →
      ∃ policy : Policy input C .native accounting Unit,
        RootPaper.Table.Core input C accounting available budget exponent policy ∧
        ChargedJointRun runtime input C accounting available budget choice.positive exponent policy ∧
        risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta

def SharpPaperClaims (runtime : RootPaper.TableCost.WordCode) : Prop :=
  ∀ (I : Instance), LaminarSchedule I.compatibility →
    ∀ (input : StatisticalInput I) (available : Finset I.Tool) (depth : Nat),
      errorRank I.compatibility available = (depth : ℕ∞) →
      ∀ epsilon : Real, 0 < epsilon → ∃ cutoff : Real, 0 < cutoff ∧
      ∀ delta : Real, 0 < delta → delta < cutoff → delta ≤ 1 / 2 →
      ∀ (budget : Rat) (exponent : Nat) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
        (C : Contract I), C.IsCurrentAllocation → ∀ accounting : NormalAccounting I,
        CompactPrice.OriginalQualification input C accounting available budget exponent →
        ∃ policy : Policy input C .native accounting Unit,
          RootPaper.Table.Core input C accounting available budget exponent policy ∧
          ChargedJointRun runtime input C accounting available budget choice.positive exponent policy ∧
          risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta ∧
          expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
            ENNReal.ofReal ((1 + epsilon) * (SymbolicPrice.inputExpression input available).eval *
              iteratedLog depth delta⁻¹)

def InfinitePaperClaims : Prop :=
  ∀ (I : Instance), LaminarSchedule I.compatibility →
    ∀ (input : StatisticalInput I) (available : Finset I.Tool), errorRank I.compatibility available = ⊤ →
    ∀ (C : Contract I), C.IsCurrentAllocation → ∀ (accounting : NormalAccounting I)
      (budget : Rat) (exponent : Nat), 0 < budget → budget ≤ 1 / 2 →
      CompactPrice.OriginalQualification input C accounting available budget exponent →
      ∃ policy : Policy input C .native accounting Unit,
        RootPaper.Table.Core input C accounting available budget exponent policy ∧
        JointWordRun input C accounting available (referenceQuota input exponent) policy ∧
        risk input C .native accounting policy.rule (Measure.dirac ()) = 0 ∧
        expectedObservationBill input C .native accounting policy.rule (Measure.dirac ()) = 0 ∧
        expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
          (min I.stageCount I.toolCount : Nat) * input.fees.maxCorrection

/-- Complete compact-controller claim at the paper's stated algorithmic
layer. All constants and the strong WORD code precede every original input.
The unrelated preserved Bool-machine target is not redefined. -/
def FullPaperClaims : Prop :=
  PreparationPaperClaims ∧ ScalarPaperClaims ∧ CompactPrice.CallbackFormulaClaims ∧
    StructuralPaperClaims ∧ SymbolicPaperClaims ∧
    ∃ runtime : RootPaper.TableCost.WordCode,
      RootPaper.TableCost.StrongWordCode runtime ∧
      0 < RootPaper.TableCost.nativeRate runtime ∧ 0 < RootPaper.TableCost.nativeDegree runtime ∧
      NativePaperClaims runtime ∧ SharpPaperClaims runtime ∧ InfinitePaperClaims

theorem head_result_of_prepared (input : StatisticalInput I) (available : Finset I.Tool)
    (laminar : LaminarSchedule I.compatibility) (prepSteps headSteps : Nat)
    (prepared : RootPaper.Table.PreparedRun I.compatibility (Finset.univ \ available) prepSteps headSteps) :
    HeadResult input available prepSteps headSteps := by
  have output := prepared.2.2.2.2.2.2
  unfold HeadResult
  dsimp only at output ⊢
  have words := RootPaper.Symbolic.read_actual_heads I.compatibility (Finset.univ \ available) _ _ output.2.2
  have spec := RootPaper.Symbolic.paper_from_original_headWords laminar input available
  rw [words]
  exact ⟨rfl, spec, spec.coefficient_exact.trans (SymbolicPrice.inputExpression_eval input available).symm⟩

theorem structural_paper_claims : StructuralPaperClaims := by
  refine ⟨RootPaper.Table.paper_table.1, ?_⟩
  intro q full laminar
  have size : treeSize q full ≤ full.length + q + 1 := by
    unfold treeSize
    split
    · omega
    · exact prepared_indexed_size_le q full
  refine ⟨size, ?_⟩
  intro used
  obtain ⟨prepSteps, headSteps, prepared⟩ := RootPaper.Table.prepared_run full laminar used
  exact ⟨prepSteps, headSteps, prepared,
    fun stages tools => prepared_heads_Nqt full used prepSteps headSteps prepared stages tools⟩

theorem symbolic_paper_claims : SymbolicPaperClaims := by
  intro I input laminar available
  obtain ⟨prepSteps, headSteps, prepared⟩ := RootPaper.Table.prepared_run I.compatibility laminar (Finset.univ \ available)
  exact ⟨prepSteps, headSteps, prepared,
    head_result_of_prepared input available laminar prepSteps headSteps prepared⟩

theorem charged_joint_of_joint (runtime : RootPaper.TableCost.WordCode)
    (input : StatisticalInput I) (C : Contract I) (laminar : LaminarSchedule I.compatibility)
    (current : C.IsCurrentAllocation) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (delta : Real) (budget : Rat) (exponent : Nat)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (policy : Policy input C .native accounting Unit)
    (rule : policy.rule = CompactPrice.tableRule input available budget (some (referenceQuota input exponent)))
    (actual : JointWordRun input C accounting available (referenceQuota input exponent) policy) :
    ChargedJointRun runtime input C accounting available budget choice.positive exponent policy := by
  obtain ⟨prepSteps, headSteps, prepared, live, symbolic⟩ := actual
  have quotas := RootPaper.TableCost.computed_quota_eq_of_choice input delta exponent budget choice
  refine ⟨prepSteps, headSteps, prepared, live, symbolic, ?_⟩
  apply RootPaper.TableCost.native_cost_on_run runtime input C laminar current accounting available
    budget choice.positive choice.small policy
  · rw [quotas]
    exact rule
  · rw [quotas]
    exact live

theorem native_paper_claims (runtime : RootPaper.TableCost.WordCode) : NativePaperClaims runtime := by
  intro I laminar input C current accounting available delta positive small budget exponent choice qualification
  obtain ⟨policy, core, actual, safe⟩ := native_symbolic input C laminar current accounting available
    delta positive small budget exponent choice qualification
  exact ⟨policy, core, charged_joint_of_joint runtime input C laminar current accounting available
    delta budget exponent choice policy core.same_rule actual, safe⟩

theorem sharp_paper_claims (runtime : RootPaper.TableCost.WordCode) : SharpPaperClaims runtime := by
  intro I laminar input available depth rank epsilon positive
  obtain ⟨cutoff, cutoffPositive, upper⟩ := sharp_symbolic I laminar input available depth rank epsilon positive
  refine ⟨cutoff, cutoffPositive, ?_⟩
  intro delta deltaPositive below small budget exponent choice C current accounting qualification
  obtain ⟨policy, core, actual, safe, bill⟩ := upper delta deltaPositive below small budget exponent choice C current accounting qualification
  exact ⟨policy, core, charged_joint_of_joint runtime input C laminar current accounting available
    delta budget exponent choice policy core.same_rule actual, safe, bill⟩

theorem infinite_paper_claims : InfinitePaperClaims := by
  intro I laminar input available rank C current accounting budget exponent positive small qualification
  exact infinite_symbolic input C laminar current accounting available rank budget exponent positive small qualification

theorem full_paper_claims : FullPaperClaims := by
  obtain ⟨runtime, strong, coefficientPositive, degreePositive, _⟩ := RootPaper.TableCost.original_cost_attachment
  refine ⟨RootPaper.Prep.ordinary_original_preparation, ?_, PSTRStatistics.callbackFormulaClaims,
    structural_paper_claims, symbolic_paper_claims, runtime, strong, coefficientPositive,
    degreePositive, native_paper_claims runtime, sharp_paper_claims runtime, infinite_paper_claims⟩
  exact ⟨RootPaper.Prep.operation_realized, fun _ S D call bounded =>
    RootPaper.TableCost.scalar_realized S D call bounded⟩

#print axioms RootPaper.L01.full_paper_claims

end RootPaper.L01
