module

public import PaperProofs.Retained.PRet_FreshHeadEntry_098
public import PaperProofs.Retained.PRet_FreshActualChoice_107
public import PaperProofs.Common.NativeBellmanChargeUpper

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshHeadBill108

open Common Common.Native PRetFreshContinuationPolicy096 PRetFreshHeadRun080 PRetFreshHeadAdvance097 PRetFreshHeadEntry098

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- The real public head output is exactly the chosen local test bit. -/
theorem written_at_testStop (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed)
    (good bad : Policy (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped
      (zeroNormalAccounting (I.freshSuffix 1)) Seed)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n) :
    let policy := twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule
    let before := (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1)).history ++ [.advanced head]
    historyWritten before head = some (test.rule.decision sample.1 (worldTapes input sample.2 head)) := by
  let policy := twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule
  have hr : run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1) =
      bellmanHeadWrittenState input (freshContract I) (zeroNormalAccounting I) head (input.truthAt sample.2)
        (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head)) :=
    run_write_at input head hhead test (postHeadRaw head good.rule bad.rule) sample n hstop
  obtain ⟨_, _, hp⟩ := run_has_prefix input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule policy.legal sample (n + 1)
  change historyWritten ((run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1)).history ++ [.advanced head]) head = _
  rw [historyWritten_append_head_advance,
    prefix_historyWritten input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample.1 _ _ hp head, hr]
  exact bellmanHeadWrittenState_written input (freshContract I) rfl (zeroNormalAccounting I) head _ _ n _

/-- All paid observations before the real continuation entry are precisely
the original local test charge; review failures and variable fees are not
silently replaced by an abstract unit-cost test. -/
theorem prefix_bill_at_testStop (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed)
    (good bad : Policy (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped
      (zeroNormalAccounting (I.freshSuffix 1)) Seed)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n) :
    let policy := twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule
    (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 2)).ledger.observationBill input.fees =
      (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) := by
  let policy := twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule
  have he := firstEntry_at_testStop input head hhead test good.rule bad.rule good.measurable_rule bad.measurable_rule sample n hstop
  have hr := run_advance_at input head hhead test good.rule bad.rule good.measurable_rule bad.measurable_rule sample n hstop
  apply bellmanPrefix_observationBill_of_entry input (freshContract I) (zeroNormalAccounting I) policy.rule policy.legal head hhead test sample (n + 2) he
  rw [hr, hstop]
  exact bellmanHeadWrittenState_reviews_eq input (freshContract I) rfl (zeroNormalAccounting I) head
    (input.truthAt sample.2) (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))

end PaperProofs.Retained.PRetFreshHeadBill108
