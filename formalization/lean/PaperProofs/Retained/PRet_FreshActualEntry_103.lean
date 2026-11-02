module

public import PaperProofs.Retained.PRet_FreshHeadAdvance_097
public import PaperProofs.Retained.PRet_FreshSuffixRun_101

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshActualEntry103

open Common Common.Native PRetFreshContinuationPolicy096 PRetFreshHeadRun080 PRetFreshHeadAdvance097

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- Every side condition for the suffix simulation is derived from the
actual finite test/write/advance prefix of the constructed full Policy. -/
theorem actual_entry_facts (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed)
    (good bad : Policy (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped
      (zeroNormalAccounting (I.freshSuffix 1)) Seed)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n) :
    let policy := twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule
    let pre := (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1)).history
    let before := pre ++ [.advanced head]
    VisibleEvent.advanced head ∉ pre ∧ historyCursor before = 1 ∧ historyWritten before head ≠ none ∧
      (∀ stage, historyWrite before (I.freshStageLift 1 stage) = none) ∧
      (∀ stage, historyReport before (I.freshStageLift 1 stage) = none) ∧
      historyCommitments before = [] ∧ historyExecutions before = [] ∧
      (∀ stage, historyObservations before (I.freshStageLift 1 stage) = []) ∧
      ReferenceSuffixView I 1 before
        (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 2))
        (initial ((input.freshSuffix 1).truthAt (referenceSuffixWorld input 1 sample.2))) := by
  let after := postHeadRaw head good.rule bad.rule
  let policy := twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule
  let written := bellmanHeadWrittenState input (freshContract I) (zeroNormalAccounting I) head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hr : run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1) = written :=
    run_write_at input head hhead test after sample n hstop
  obtain ⟨_, _, hp⟩ := run_has_prefix input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule policy.legal sample (n + 1)
  rw [hr] at hp
  have hc : written.cursor = 0 := bellmanHeadWrittenState_cursor input (freshContract I) (zeroNormalAccounting I) head _ _ n _
  have hw := bellmanHeadWrittenState_written input (freshContract I) rfl (zeroNormalAccounting I) head
    (input.truthAt sample.2) (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hhc : historyCursor written.history = 0 :=
    (prefix_historyCursor input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample.1 _ _ hp).trans hc
  have hclean := bellmanEntry_future_clean_of_prefix input (freshContract I) rfl .uncapped (zeroNormalAccounting I)
    policy.rule sample.1 _ _ hp head hc
  have hlogs := bellmanHeadWrittenState_history_corrections input (freshContract I) rfl (zeroNormalAccounting I) head
    (input.truthAt sample.2) (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have ha := run_advance_at input head hhead test good.rule bad.rule good.measurable_rule bad.measurable_rule sample n hstop
  change run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 2) =
    record (zeroNormalAccounting I) written (.advance head) [.advanced head] (advanceLedger written head) 1 false at ha
  have hr' : run input (freshContract I) .uncapped (zeroNormalAccounting I)
      (twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule).rule sample (n + 1) = written := hr
  have ha' : run input (freshContract I) .uncapped (zeroNormalAccounting I)
      (twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule).rule sample (n + 2) =
      record (zeroNormalAccounting I) written (.advance head) [.advanced head] (advanceLedger written head) 1 false := ha
  dsimp only
  rw [hr']
  refine ⟨not_mem_advanced_of_historyCursor_zero written.history hhc head, ?_, ?_,
    fun stage => (hclean stage).2.1, fun stage => (hclean stage).2.2, ?_, ?_, fun stage => (hclean stage).1, ?_⟩
  · rw [historyCursor_append_head_advance, hhc]
  · rw [historyWritten_append_head_advance,
      prefix_historyWritten input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample.1 _ _ hp head, hw]
    exact Option.some_ne_none _
  · simpa only [historyCommitments, List.filterMap_append, List.filterMap_cons,
      eventCommitment, List.filterMap_nil, List.append_nil] using hlogs.1
  · simpa only [historyExecutions, List.filterMap_append, List.filterMap_cons,
      eventExecution, List.filterMap_nil, List.append_nil] using hlogs.2
  · obtain ⟨_, _, hpa⟩ := run_has_prefix input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule policy.legal sample (n + 2)
    have hview := suffixInitialView_of_prefix input 1 (freshContract I) (zeroNormalAccounting I) policy.rule sample.1 _ _ hpa
      (by rw [ha]; rfl) (by rw [ha]; rfl) ((input.freshSuffix 1).truthAt (referenceSuffixWorld input 1 sample.2))
    rw [ha']
    simpa only [ha, record] using hview

end PaperProofs.Retained.PRetFreshActualEntry103
