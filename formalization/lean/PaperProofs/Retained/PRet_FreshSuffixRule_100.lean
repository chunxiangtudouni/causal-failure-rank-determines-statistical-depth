module

public import PaperProofs.Retained.PRet_FreshSuffixSelection_099
public import PaperProofs.Retained.PRet_RetainedSuffixGuard_078

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshSuffixRule100

open Common Common.Native PRetFreshContinuationPolicy096 PRetFreshSuffixSelection099
open PRetRetainedGuard007 PRetRetainedSuffixGuard078

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- A lawful actual child action is the actual guarded parent action.
The public head cut preserves both original continuation branches and the
terminal retained allocation permissions. -/
theorem rule_join (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed)
    (good bad : PolicyRule (I.freshSuffix 1) Seed) (seed : Seed)
    (pre : List (VisibleEvent I)) (hn : VisibleEvent.advanced head ∉ pre)
    (hc : historyCursor (pre ++ [.advanced head]) = 1)
    (hw : historyWritten (pre ++ [.advanced head]) head ≠ none)
    (hwrite : ∀ stage, historyWrite (pre ++ [.advanced head]) (I.freshStageLift 1 stage) = none)
    (hreport : ∀ stage, historyReport (pre ++ [.advanced head]) (I.freshStageLift 1 stage) = none)
    (hcommit : historyCommitments (pre ++ [.advanced head]) = [])
    (hexec : historyExecutions (pre ++ [.advanced head]) = [])
    (after : List (VisibleEvent (I.freshSuffix 1)))
    (hallow : allows after ((if historyWritten (pre ++ [.advanced head]) head =
      (historyReport (pre ++ [.advanced head]) head).map Prod.fst then good else bad) seed after)) :
    PRetFreshHeadPolicy079.rule input head test (postHeadRaw head good bad) seed
      (referenceSuffixHistoryJoin I 1 (pre ++ [.advanced head]) after) =
      referenceSuffixActionLift I 1 (historyActions (pre ++ [.advanced head])).length
        ((if historyWritten (pre ++ [.advanced head]) head =
          (historyReport (pre ++ [.advanced head]) head).map Prod.fst then good else bad) seed after) := by
  have hearly : head.val < 1 := by omega
  have hraw : bellmanHeadThenRaw input head test (postHeadRaw head good bad) seed
      (referenceSuffixHistoryJoin I 1 (pre ++ [.advanced head]) after) =
      referenceSuffixActionLift I 1 (historyActions (pre ++ [.advanced head])).length
        ((if historyWritten (pre ++ [.advanced head]) head =
          (historyReport (pre ++ [.advanced head]) head).map Prod.fst then good else bad) seed after) := by
    simp only [bellmanHeadThenRaw, historyWritten_referenceSuffixJoin_earlier 1 head hearly, hw, ite_false]
    exact postHeadRaw_join head hhead good bad seed pre hn hc after
  have ha := allows_referenceSuffixJoin I 1 (pre ++ [.advanced head]) after hc hwrite hreport hcommit hexec _ hallow
  change guarded _ seed _ = _
  simp only [guarded, hraw, ha, ite_true]

end PaperProofs.Retained.PRetFreshSuffixRule100
