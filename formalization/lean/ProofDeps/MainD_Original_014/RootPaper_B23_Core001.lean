module

public import RootPaper_Prep_Algorithm001
import Lean.Util.CollectAxioms

/-! The paper preparation is connected to the SAME original bounded
reference policy and its original resource qualification. No computational
cost theorem is asserted here; the separate actual-work composition remains
necessary for full B23. Existing strengthened Bool-machine claims are intact. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open MeasureTheory
open scoped BigOperators ENNReal

namespace RootPaper.B23

open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RationalControllerComputation

variable {I : Instance}

structure Core (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : Rat) (exponent : Nat)
    (policy : Policy input C .native accounting Unit) : Prop where
  exponent_eq : computedExponent (I := I) budget = exponent
  numeric_check : numericQualification input C budget = true
  preparation_output : ∀ positive : 0 < budget,
    RootPaper.Prep.preparation input C budget positive = preparationOutput input C budget
  same_rule : policy.rule = referenceRule input available budget (some (referenceQuota input exponent))
  same_run : ∀ sample clock, run input C .native accounting policy.rule sample clock =
    run input C .uncapped accounting
      (referenceRule input available budget (some (referenceQuota input exponent))) sample clock
  normal_calls : NormalCallCertificate input C .native accounting policy C.normalCallBound
  caps : ∀ sample clock, (run input C .native accounting policy.rule sample clock).ledger.obeysCaps C
  halted : ∀ sample,
    (run input C .native accounting policy.rule sample
      (quotaActionBound I (referenceQuota input exponent) + 1)).halted = true

/-- Numeric qualification is computed from the original caps. Complete H0
is retained as the separate original assumption, never inferred from bits. -/
theorem numeric_check_of_qualification (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : Rat) (exponent : Nat)
    (sameExponent : computedExponent (I := I) budget = exponent)
    (qualification : ReferenceCompleteOriginalQualification input C hearly accounting available budget exponent) :
    numericQualification input C budget = true := by
  unfold numericQualification computedQuotas
  rw [sameExponent]
  exact decide_eq_true_eq.mpr ⟨qualification.stage_quota, qualification.total_calls⟩

/-- Every available set uses the already constructed original native
policy. All clocks and all samples are preserved, including failure paths. -/
theorem core (input : StatisticalInput I) (C : Contract I) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (delta : Real)
    (budget : Rat) (exponent : Nat) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : ReferenceCompleteOriginalQualification input C current.1 accounting available budget exponent) :
    Core input C accounting available budget exponent
      (GeneralNormalFees.completeNativeReferencePolicy input C current.1 accounting available budget exponent qualification) := by
  let policy := GeneralNormalFees.completeNativeReferencePolicy input C current.1 accounting available budget exponent qualification
  obtain ⟨witness, rule, runs, normal, _resources⟩ :=
    referenceCompleteResourceClaims input C current.1 accounting available budget exponent
      choice.positive choice.small qualification
  have same : policy.rule = witness.rule :=
    (GeneralNormalFees.completeNativeReferencePolicy_rule input C current.1 accounting available budget exponent qualification).trans rule.symm
  have sameRun : ∀ sample clock, run input C .native accounting policy.rule sample clock =
      run input C .uncapped accounting
        (referenceRule input available budget (some (referenceQuota input exponent))) sample clock := by
    intro sample clock
    rw [same]
    exact runs sample clock
  refine ⟨choice.same_exponent,
    numeric_check_of_qualification input C current.1 accounting available budget exponent choice.same_exponent qualification,
    fun positive => RootPaper.Prep.preparation_eq I input C budget positive,
    GeneralNormalFees.completeNativeReferencePolicy_rule input C current.1 accounting available budget exponent qualification,
    sameRun, ?_, ?_, ?_⟩
  · intro sample clock
    change (run input C .native accounting policy.rule sample clock).ledger.normalCalls ≤ _
    rw [same]
    exact normal sample clock
  · intro sample clock
    exact run_native_obeysCaps input C accounting policy.rule policy.legal sample clock
  · intro sample
    rw [sameRun]
    exact referenceBounded_halted input C current.1 accounting available budget exponent sample

/-- The original full starting tool set also retains the actual native
risk and full expected-bill comparison. No success conditioning is added. -/
theorem statistical_core (input : StatisticalInput I) (C : Contract I) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (delta : Real) (positive : 0 < delta) (small : delta ≤ 1 / 2)
    (budget : Rat) (exponent : Nat) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : ReferenceCompleteOriginalQualification input C current.1 accounting I.tools budget exponent) :
    let policy := GeneralNormalFees.completeNativeReferencePolicy input C current.1 accounting I.tools budget exponent qualification
    Core input C accounting I.tools budget exponent policy ∧
      risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta ∧
      expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
        expectedBill input C .uncapped accounting
          (referenceIdealPolicy input C current.1 accounting I.tools budget).rule (Measure.dirac ()) := by
  exact ⟨core input C current accounting I.tools delta budget exponent choice qualification,
    GeneralNormalFees.completeNativeReferencePolicy_performance input C current accounting delta positive small
      exponent budget choice qualification⟩

end RootPaper.B23

#print axioms RootPaper.B23.core
#print axioms RootPaper.B23.statistical_core

open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let declarations := env.constants.toList.filter (fun (name, _) =>
    name.toString.startsWith "RootPaper.B23.")
  unless declarations.length > 0 do throwError "ROOT_PAPER_B23_STD3_FAIL no own declarations"
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut theorems : Nat := 0
  for (name, info) in declarations do
    match info with
    | .axiomInfo _ => throwError m!"ROOT_PAPER_B23_STD3_FAIL new_axiom={name}"
    | .opaqueInfo _ => throwError m!"ROOT_PAPER_B23_STD3_FAIL opaque={name}"
    | .thmInfo _ => theorems := theorems + 1
    | _ => pure ()
    for ax in ← collectAxioms name do
      unless allowed.contains ax do throwError m!"ROOT_PAPER_B23_STD3_FAIL forbidden={ax} declaration={name}"
  logInfo m!"ROOT_PAPER_B23_STD3_PASS declarations={declarations.length} theorems={theorems} new_axioms=0 forbidden=0"
