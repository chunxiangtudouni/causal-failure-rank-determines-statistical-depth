module

public import PaperProofs.Retained.PRet_FreshActualRun_106

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshActualChoice107

open Common Common.Native PRetFreshContinuationPolicy096 PRetFreshHeadRun080

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- The actual public continuation selector is exactly the local test's
true correct/error event, recovered from its real early write and report. -/
theorem choice_at_testStop (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed)
    (good bad : Policy (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped
      (zeroNormalAccounting (I.freshSuffix 1)) Seed)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n) :
    let policy := twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule
    let before := (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1)).history ++ [.advanced head]
    historyWritten before head = (historyReport before head).map Prod.fst ↔
      test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head := by
  let after := postHeadRaw head good.rule bad.rule
  let policy := twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule
  let written := bellmanHeadWrittenState input (freshContract I) (zeroNormalAccounting I) head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hr : run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1) = written :=
    run_write_at input head hhead test after sample n hstop
  obtain ⟨_, _, hp⟩ := run_has_prefix input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule policy.legal sample (n + 1)
  rw [hr] at hp
  have ht := prefix_truth input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample.1 _ _ hp
  have hw := bellmanHeadWrittenState_written input (freshContract I) rfl (zeroNormalAccounting I) head
    (input.truthAt sample.2) (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hreport : ∃ clock, written.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input (zeroNormalAccounting I) head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [written, bellmanHeadWrittenState, record, reportedWriteLedger, freshContract, ↓reduceIte,
      writeLedger, Function.update_self]
  obtain ⟨clock, hreport⟩ := hreport
  change historyWritten ((run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1)).history ++ [.advanced head]) head = _ ↔ _
  rw [hr, historyWritten_append_head_advance, historyReport_append_head_advance,
    prefix_historyWritten input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample.1 _ _ hp head,
    prefix_historyReport_early input (freshContract I) rfl .uncapped (zeroNormalAccounting I) policy.rule sample.1 _ _ hp head,
    hw, hreport, Option.map_some, ht]
  change some (test.rule.decision sample.1 (worldTapes input sample.2 head)) =
    some (input.truthAt sample.2 head) ↔ _
  exact ⟨Option.some.inj, congrArg some⟩

end PaperProofs.Retained.PRetFreshActualChoice107
