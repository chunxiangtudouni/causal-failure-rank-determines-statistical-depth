module

public import PaperProofs.Retained.PRet_FreshSuffixRule_100
public import PaperProofs.Retained.PRet_ActiveSuffixRun_102

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshSuffixRun101

open Common Common.Native PRetFreshContinuationPolicy096 PRetFreshSuffixRule100 PRetActiveSuffixRun102

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- Genuine legal child prefixes and the actual public head history imply
full all-clock run transport. Terminal allocations and failed/nonreturning
child runs are covered by the same actual interpreter equality. -/
theorem actual_run_view (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed)
    (good bad : Policy (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped
      (zeroNormalAccounting (I.freshSuffix 1)) Seed)
    (sample : Seed × input.World) (pre : List (VisibleEvent I))
    (hn : VisibleEvent.advanced head ∉ pre)
    (hc : historyCursor (pre ++ [.advanced head]) = 1)
    (hw : historyWritten (pre ++ [.advanced head]) head ≠ none)
    (hwrite : ∀ stage, historyWrite (pre ++ [.advanced head]) (I.freshStageLift 1 stage) = none)
    (hreport : ∀ stage, historyReport (pre ++ [.advanced head]) (I.freshStageLift 1 stage) = none)
    (hcommit : historyCommitments (pre ++ [.advanced head]) = [])
    (hexec : historyExecutions (pre ++ [.advanced head]) = [])
    (hobs : ∀ stage, historyObservations (pre ++ [.advanced head]) (I.freshStageLift 1 stage) = [])
    (start : ℕ)
    (hstart : ReferenceSuffixView I 1 (pre ++ [.advanced head])
      (run input (freshContract I) .uncapped (zeroNormalAccounting I)
        (twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule).rule sample start)
      (initial ((input.freshSuffix 1).truthAt (referenceSuffixWorld input 1 sample.2)))) :
    let child := if historyWritten (pre ++ [.advanced head]) head =
      (historyReport (pre ++ [.advanced head]) head).map Prod.fst then good else bad
    ∀ k, ReferenceSuffixView I 1 (pre ++ [.advanced head])
      (run input (freshContract I) .uncapped (zeroNormalAccounting I)
        (twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule).rule sample (start + k))
      (run (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped (zeroNormalAccounting (I.freshSuffix 1))
        child.rule (sample.1, referenceSuffixWorld input 1 sample.2) k) := by
  classical
  let policy := twoContinuationPolicy input head test good.rule bad.rule good.measurable_rule bad.measurable_rule
  let child := if historyWritten (pre ++ [.advanced head]) head =
    (historyReport (pre ++ [.advanced head]) head).map Prod.fst then good else bad
  change ∀ k, ReferenceSuffixView I 1 (pre ++ [.advanced head])
    (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (start + k))
    (run (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped (zeroNormalAccounting (I.freshSuffix 1))
      child.rule (sample.1, referenceSuffixWorld input 1 sample.2) k)
  have hstart' : ReferenceSuffixView I 1 (pre ++ [VisibleEvent.advanced head])
      (run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample start)
      (initial ((input.freshSuffix 1).truthAt (referenceSuffixWorld input 1 sample.2))) := hstart
  refine suffixRun_view_of_active_rule_lift input 1 (freshContract I) rfl (zeroNormalAccounting I) policy.rule policy.legal
    (freshContract (I.freshSuffix 1)) rfl (zeroNormalAccounting (I.freshSuffix 1)) child.rule child.legal
    sample (pre ++ [VisibleEvent.advanced head]) start hobs hstart' ?_
  intro k hv ha
  obtain ⟨m, _, hp⟩ := run_has_prefix (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped
    (zeroNormalAccounting (I.freshSuffix 1)) child.rule child.legal (sample.1, referenceSuffixWorld input 1 sample.2) k
  obtain ⟨next, hs⟩ := child.legal sample.1 _ _ m _ hp ha
  have hallow := PRetRetainedGuard007.allows_of_step (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) rfl
    (zeroNormalAccounting (I.freshSuffix 1)) child.rule sample.1 _ _ hp hs
  let after := (run (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped
    (zeroNormalAccounting (I.freshSuffix 1)) child.rule (sample.1, referenceSuffixWorld input 1 sample.2) k).history
  have hrule : child.rule =
      if historyWritten (pre ++ [VisibleEvent.advanced head]) head =
        (historyReport (pre ++ [VisibleEvent.advanced head]) head).map Prod.fst then good.rule else bad.rule := by
    dsimp only [child]
    split_ifs <;> rfl
  have hallow' : PRetRetainedGuard007.allows after
      ((if historyWritten (pre ++ [VisibleEvent.advanced head]) head =
        (historyReport (pre ++ [VisibleEvent.advanced head]) head).map Prod.fst then good.rule else bad.rule) sample.1 after) := by
    change PRetRetainedGuard007.allows after (child.rule sample.1 after) at hallow
    rw [hrule] at hallow
    exact hallow
  have hjoin := rule_join input head hhead test good.rule bad.rule sample.1 pre hn hc hw hwrite hreport hcommit hexec after hallow'
  rw [hv.history]
  change PRetFreshHeadPolicy079.rule input head test (postHeadRaw head good.rule bad.rule) sample.1
    (referenceSuffixHistoryJoin I 1 (pre ++ [VisibleEvent.advanced head]) after) =
    referenceSuffixActionLift I 1 (historyActions (pre ++ [VisibleEvent.advanced head])).length (child.rule sample.1 after)
  rw [hrule]
  exact hjoin

end PaperProofs.Retained.PRetFreshSuffixRun101
