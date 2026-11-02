module

public import RootPaper_Table_Main001
public import RootPaper_Symbolic_Actual003
import Lean.Util.CollectAxioms

/-! Same-witness paper composition. The actual TABLE execution, heads and
symbolic constructor share one P witness and one prepared heap. The original
native/sharp/infinite policies retain their original qualifications. Scalar
preparation and online arithmetic costs remain separate necessary work. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open MeasureTheory
open scoped ENNReal

namespace RootPaper.L01

open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open PaperProofs.Structure PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims PA17A19RuntimeEntry020

variable {I : Instance}

def HeadResult (input : StatisticalInput I) (available : Finset I.Tool)
    (prepSteps headSteps : Nat) : Prop :=
  let after := packingRun (callInput I.toolCount I.compatibility .query) RootPaper.Table.heads headSteps
    (packingInitial (RootPaper.Table.preparedHeap I.compatibility (Finset.univ \ available) prepSteps))
  let words := RootPaper.Symbolic.readHeadWords after.heap (after.register .index).toNat
  let output := RootPaper.Symbolic.fromHeadWords input words
  words = CompactPrice.headWords I.toolCount I.compatibility (Finset.univ \ available) ∧
    RootPaper.Symbolic.PaperSpec input available output ∧
    output.built.expression.eval = (SymbolicPrice.inputExpression input available).eval

def JointWordRun (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (quota : I.Stage → Nat)
    (policy : Policy input C .native accounting Unit) : Prop :=
  ∃ prepSteps headSteps,
    RootPaper.Table.PreparedRun I.compatibility (Finset.univ \ available) prepSteps headSteps ∧
    RootPaper.Table.NativeWordRun input C accounting available quota policy
      (RootPaper.Table.preparedHeap I.compatibility (Finset.univ \ available) prepSteps) ∧
    HeadResult input available prepSteps headSteps

/-- This local transport consumes actual TABLE witnesses internally.
The main theorems below discharge WordRun and never ask callers for heads,
heap correctness, a statistical bound or a computational cost oracle. -/
theorem joint_of_word_run (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (quota : I.Stage → Nat)
    (policy : Policy input C .native accounting Unit)
    (actual : RootPaper.Table.WordRun input C accounting available quota policy) :
    JointWordRun input C accounting available quota policy := by
  obtain ⟨prepSteps, headSteps, prepared, live⟩ := actual
  refine ⟨prepSteps, headSteps, prepared, live, ?_⟩
  have output := prepared.2.2.2.2.2.2
  unfold HeadResult
  dsimp only at output ⊢
  have words := RootPaper.Symbolic.read_actual_heads I.compatibility (Finset.univ \ available) _ _ output.2.2
  have spec := RootPaper.Symbolic.paper_from_original_headWords laminar input available
  rw [words]
  exact ⟨rfl, spec, spec.coefficient_exact.trans (SymbolicPrice.inputExpression_eval input available).symm⟩

theorem native_symbolic (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (delta : Real)
    (positive : 0 < delta) (small : delta ≤ 1 / 2) (budget : Rat) (exponent : Nat)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : CompactPrice.OriginalQualification input C accounting available budget exponent) :
    ∃ policy : Policy input C .native accounting Unit,
      RootPaper.Table.Core input C accounting available budget exponent policy ∧
      JointWordRun input C accounting available (referenceQuota input exponent) policy ∧
      risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta := by
  obtain ⟨policy, core, actual, safe⟩ := RootPaper.Table.native_claims I laminar input C current accounting
    available delta positive small budget exponent choice qualification
  exact ⟨policy, core, joint_of_word_run input C laminar accounting available _ policy actual, safe⟩

theorem sharp_symbolic (I : Instance) (laminar : LaminarSchedule I.compatibility)
    (input : StatisticalInput I) (available : Finset I.Tool) (depth : Nat)
    (rank : errorRank I.compatibility available = (depth : ℕ∞)) (epsilon : Real) (positive : 0 < epsilon) :
    ∃ cutoff : Real, 0 < cutoff ∧ ∀ delta : Real, 0 < delta → delta < cutoff → delta ≤ 1 / 2 →
      ∀ (budget : Rat) (exponent : Nat), ReferenceRiskChoice I.stageCount delta exponent budget →
      ∀ (C : Contract I), C.IsCurrentAllocation → ∀ accounting : NormalAccounting I,
        CompactPrice.OriginalQualification input C accounting available budget exponent →
        ∃ policy : Policy input C .native accounting Unit,
          RootPaper.Table.Core input C accounting available budget exponent policy ∧
          JointWordRun input C accounting available (referenceQuota input exponent) policy ∧
          risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta ∧
          expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
            ENNReal.ofReal ((1 + epsilon) * (SymbolicPrice.inputExpression input available).eval *
              iteratedLog depth delta⁻¹) := by
  obtain ⟨cutoff, cutoffPositive, upper⟩ := RootPaper.Table.sharp_claims I laminar input available depth rank epsilon positive
  refine ⟨cutoff, cutoffPositive, ?_⟩
  intro delta deltaPositive below small budget exponent choice C current accounting qualification
  obtain ⟨policy, core, actual, safe, bill⟩ := upper delta deltaPositive below small budget exponent choice C current accounting qualification
  exact ⟨policy, core, joint_of_word_run input C laminar accounting available _ policy actual, safe, bill⟩

theorem infinite_symbolic (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (rank : errorRank I.compatibility available = ⊤) (budget : Rat) (exponent : Nat)
    (positive : 0 < budget) (small : budget ≤ 1 / 2)
    (qualification : CompactPrice.OriginalQualification input C accounting available budget exponent) :
    ∃ policy : Policy input C .native accounting Unit,
      RootPaper.Table.Core input C accounting available budget exponent policy ∧
      JointWordRun input C accounting available (referenceQuota input exponent) policy ∧
      risk input C .native accounting policy.rule (Measure.dirac ()) = 0 ∧
      expectedObservationBill input C .native accounting policy.rule (Measure.dirac ()) = 0 ∧
      expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
        (min I.stageCount I.toolCount : Nat) * input.fees.maxCorrection := by
  obtain ⟨policy, core, actual, safe, observations, bill⟩ := RootPaper.Table.infinite_claims I laminar input
    available rank C current accounting budget exponent positive small qualification
  exact ⟨policy, core, joint_of_word_run input C laminar accounting available _ policy actual, safe, observations, bill⟩

end RootPaper.L01

#print axioms RootPaper.L01.native_symbolic
#print axioms RootPaper.L01.sharp_symbolic
#print axioms RootPaper.L01.infinite_symbolic
#print axioms RootPaper.Symbolic.actual_original_paper_symbolic

open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let declarations := env.constants.toList.filter (fun (name, _) =>
    name.toString.startsWith "RootPaper.L01.")
  unless declarations.length > 0 do throwError "ROOT_PAPER_L01_STD3_FAIL no declarations"
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut theorems : Nat := 0
  for (name, info) in declarations do
    match info with
    | .axiomInfo _ => throwError m!"ROOT_PAPER_L01_STD3_FAIL new_axiom={name}"
    | .opaqueInfo _ => throwError m!"ROOT_PAPER_L01_STD3_FAIL opaque={name}"
    | .thmInfo _ => theorems := theorems + 1
    | _ => pure ()
    for ax in ← collectAxioms name do
      unless allowed.contains ax do throwError m!"ROOT_PAPER_L01_STD3_FAIL forbidden={ax} declaration={name}"
  -- Imported generated equation headers are not new source axioms. Audit
  -- the actual consumed imported proof endpoints by their dependencies.
  let imported := #[`RootPaper.Symbolic.actual_original_paper_symbolic,
    `RootPaper.Symbolic.paper_from_original_headWords, `RootPaper.Symbolic.read_actual_heads]
  for name in imported do
    for ax in ← collectAxioms name do
      unless allowed.contains ax do throwError m!"ROOT_PAPER_L01_STD3_FAIL forbidden={ax} imported={name}"
  logInfo m!"ROOT_PAPER_L01_STD3_PASS declarations={declarations.length} theorems={theorems} imported_endpoints={imported.size} new_axioms=0 forbidden=0"
