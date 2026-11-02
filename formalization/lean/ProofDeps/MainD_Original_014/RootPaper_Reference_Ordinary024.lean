module
public import RootPaper_Reference_NativeCost023
import Lean.Util.CollectAxioms

/-! Ordinary boundary consumer of the complete paper-level reference
algorithm, original preparation, same-prefix action and all-path bit fees. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RationalControllerComputation

theorem ordinary_paper_reference :
    ∃ runtime : WordRuntime,0<globalRate runtime ∧ 0<globalDegree runtime ∧
      ∀ (I : Instance) (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
        (budget : Rat) (positive : 0<budget) (_small : budget≤1/2),
        (prepareOnce input C available budget positive).1.value=
          ⟨computedExponent (I:=I) budget,RootPaper.Prep.originalRows input budget,numericQualification input C budget⟩ ∧
        (∀ (accounting : NormalAccounting I) (_early : C.reporting=.early) (seed : Unit)
          (truth : I.Stage→Bool) (tapes : ReviewTapes input) (n : Nat) (state : State I),
          Prefix input C .uncapped accounting
            (referenceRule input available budget (some (computedQuotas input budget))) seed truth tapes n state→
          ((prepareOnce input C available budget positive).2 state.history).action=
            referenceRule input available budget (some (computedQuotas input budget)) seed state.history) ∧
        ∀ (accounting : NormalAccounting I) (_early : C.reporting=.early)
          (policy : Policy input C .native accounting Unit) (sample : Unit×input.World),
          totalRunningCost runtime input C accounting policy available budget positive sample≤
            generalStructureFactor I*globalRate runtime*(arithmeticScale input C budget)^globalDegree runtime :=
  paper_reference_accounted

theorem ordinary_native_reference (runtime : WordRuntime) {I : Instance} (input : StatisticalInput I)
    (C : Contract I) (current : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (delta : Real) (budget : Rat) (exponent : Nat)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : ReferenceCompleteOriginalQualification input C current.1 accounting available budget exponent) :
    let policy:=GeneralNormalFees.completeNativeReferencePolicy input C current.1 accounting available budget exponent qualification
    RootPaper.B23.Core input C accounting available budget exponent policy ∧
    (∀ sample clock,
      ((prepareOnce input C available budget choice.positive).2
        (run input C .native accounting policy.rule sample clock).history).action=
          policy.rule sample.1 (run input C .native accounting policy.rule sample clock).history) ∧
    ∀ sample,totalRunningCost runtime input C accounting policy available budget choice.positive sample≤
      generalStructureFactor I*globalRate runtime*(arithmeticScale input C budget)^globalDegree runtime := by
  dsimp only
  let policy:=GeneralNormalFees.completeNativeReferencePolicy input C current.1 accounting available budget exponent qualification
  have core:=RootPaper.B23.core input C current accounting available delta budget exponent choice qualification
  have quotas : computedQuotas input budget=referenceQuota input exponent := by
    unfold computedQuotas
    rw [core.exponent_eq]
  refine ⟨core,?_,?_⟩
  · intro sample clock
    have sameRun :=core.same_run sample clock
    rw [←quotas] at sameRun
    rw [sameRun,core.same_rule,←quotas]
    obtain ⟨n,_before,hp⟩:=run_has_prefix input C .uncapped accounting
      (referenceRule input available budget (some (computedQuotas input budget)))
      (referenceRule_uncapped_legal input C current.1 accounting available budget (some (computedQuotas input budget))) sample clock
    exact initialized_same_rule input C current.1 accounting available budget choice.positive choice.small sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hp
  · intro sample
    exact totalRunningCost_bound runtime input C current.1 accounting policy available budget choice.positive choice.small sample

end RootPaper.Reference.Charged

#print axioms RootPaper.Reference.Charged.ordinary_paper_reference
#print axioms RootPaper.Reference.Charged.word_realized
#print axioms RootPaper.Reference.Charged.calculation_scalar_realized
#print axioms RootPaper.Reference.Charged.initial_visited_data
#print axioms RootPaper.Reference.Charged.ordinary_native_reference

open Lean Elab Command
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let endpoints := #[`RootPaper.Reference.Charged.ordinary_paper_reference,
    `RootPaper.Reference.Charged.word_realized,
    `RootPaper.Reference.Charged.calculation_scalar_realized,
    `RootPaper.Reference.Charged.initial_visited_data,
    `RootPaper.Reference.Charged.ordinary_native_reference]
  for endpoint in endpoints do
    for axiomName in ← collectAxioms endpoint do
      unless allowed.contains axiomName do
        throwError m!"ROOT_PAPER_REFERENCE_ORDINARY_FAIL declaration={endpoint} axiom={axiomName}"
  logInfo "ROOT_PAPER_REFERENCE_ORDINARY_STD3_PASS endpoints=5 forbidden=0"
