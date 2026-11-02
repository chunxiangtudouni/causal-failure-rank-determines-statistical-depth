module

public import PaperProofs.Paid.BridgeClaims
public import PaperProofs.Common.NativeHorizon

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDLower

variable {I : Instance}

theorem step_tapes_irrelevant_of_zero_quota (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (hquota : ∀ stage, C.reviewQuota stage = 0)
    (tapes tapes' : ReviewTapes input) {state next : State I} {action : Action I}
    (step : Step input C .native accounting tapes state action next) :
    Step input C .native accounting tapes' state action next := by
  cases step with
  | review stage live port resources =>
    rcases resources with impossible | caps
    · cases impossible
    · have hbound := caps.1 stage
      simp only [record, reviewLedger, Function.update_self] at hbound
      rw [hquota stage, Nat.cast_zero] at hbound
      have hpositive : (0 : ℕ∞) < state.ledger.reviews stage + 1 := by positivity
      exact ((not_lt_of_ge hbound) hpositive).elim
  | write stage bit live port resources => exact .write state stage bit live port resources
  | allocate handle tool active valid compatible unused unallocated window resources =>
    exact .allocate state handle tool active valid compatible unused unallocated window resources
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    exact .execute state handle tool active valid compatible committed unused uncorrected window resources
  | advance stage live written resources => exact .advance state stage live written resources
  | stop active => exact .stop state active
  | abandon active => exact .abandon state active

theorem zero_quota_run_reviews (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (hquota : ∀ stage, C.reviewQuota stage = 0)
    {Seed : Type*} [MeasurableSpace Seed] (policy : Policy input C .native accounting Seed)
    (sample : Seed × input.World) (n : ℕ) (stage : I.Stage) :
    (run input C .native accounting policy.rule sample n).ledger.reviews stage = 0 := by
  obtain ⟨_clock, _hclock, path⟩ :=
    run_has_prefix input C .native accounting policy.rule policy.legal sample n
  have hbound := (prefix_native_obeysCaps input C accounting policy.rule sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) path).1 stage
  rw [hquota stage, Nat.cast_zero] at hbound
  exact le_antisymm hbound bot_le

end PDLower
