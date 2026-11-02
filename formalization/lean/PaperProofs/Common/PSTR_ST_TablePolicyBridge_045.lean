module

public import PaperProofs.Common.PSTR_ST_SharpUpperClaims_043

/-! Transfer the already proved ORIGINAL TABLE statistics to any concrete
policy with exactly the same rule. Legal/measurable proof fields are not
new runtime inputs. No machine cost or generic-picker run is assumed. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.CompactABI

open PaperProofs.Structure.LaminarTree
open CompactPrice

variable {I : Instance}

theorem policy_eq_of_rule_eq {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (left right : Policy input C mode accounting Seed)
    (hrule : left.rule = right.rule) : left = right := by
  cases left
  cases right
  cases hrule
  rfl

theorem actualCompactCost_iff_of_rule_eq
    (constant wordFactor scratchFactor degree : Nat) (implementation : CompactPrice.Implementation)
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (exponent : Nat)
    (left right : Policy input C .native accounting Unit) (hrule : left.rule = right.rule) :
    ActualCompactCost constant wordFactor scratchFactor degree implementation input C accounting
      available budget exponent left ↔
    ActualCompactCost constant wordFactor scratchFactor degree implementation input C accounting
      available budget exponent right := by
  have hpolicy := policy_eq_of_rule_eq input C .native accounting left right hrule
  cases hpolicy
  rfl

theorem tablePolicy_statistics (input : StatisticalInput I)
    (hlaminar : LaminarSchedule I.compatibility) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ 1 / 2) (budget : ℚ) (exponent : Nat)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : OriginalQualification input C accounting available budget exponent)
    (policy : Policy input C .native accounting Unit)
    (hrule : policy.rule = tableRule input available budget (some (referenceQuota input exponent))) :
    (∀ sample clock, run input C .native accounting policy.rule sample clock =
      run input C .uncapped accounting
        (tableRule input available budget (some (referenceQuota input exponent))) sample clock) ∧
    (∀ sample clock, (run input C .native accounting policy.rule sample clock).ledger.obeysCaps C ∧
      (run input C .native accounting policy.rule sample clock).ledger.normalCalls ≤ (C.normalCallBound : ℕ∞)) ∧
    risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta ∧
    expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
      expectedBill input C .uncapped accounting (tableRule input available budget none) (Measure.dirac ()) := by
  obtain ⟨canonical, hcanonical, hrun, hcaps, hrisk, hbill⟩ :=
    TableNativeRisk.tableNativeStatisticalClaims input hlaminar C hcurrent accounting available
      delta hd hsmall budget exponent choice qualification
  have hpolicy := policy_eq_of_rule_eq input C .native accounting policy canonical
    (hrule.trans hcanonical.symm)
  cases hpolicy
  exact ⟨hrun, hcaps, hrisk, hbill⟩

theorem tablePolicy_halted (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (quota : I.Stage → Nat)
    (policy : Policy input C .native accounting Unit)
    (hrule : policy.rule = tableRule input available budget (some quota)) (sample : Unit × input.World) :
    (run input C .native accounting policy.rule sample (quotaActionBound I quota + 1)).halted = true := by
  have hs := (run_uncapped_eq_native input C accounting policy.rule policy.legal sample
    (quotaActionBound I quota + 1)).symm
  have ht := congrArg (fun rule : PolicyRule I Unit =>
    run input C .uncapped accounting rule sample (quotaActionBound I quota + 1)) hrule
  exact (congrArg (fun state : State I => state.halted) (hs.trans ht)).trans
    (tableRule_halted input C hearly accounting available budget quota sample)

end PaperProofs.Common.Native.PSTRStatistics.CompactABI
