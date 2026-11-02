module

public import PaperProofs.Retained.PRet_FreshContinuationPolicy_096
public import PaperProofs.Common.NativeBellmanHistoryLift

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshSuffixSelection099

open Common Common.Native PRetFreshContinuationPolicy096

variable {I : Instance} {Seed : Type*}

/-- The actual post-head public history split recovers its exact chosen
fresh child, with original private seed, labels and visible serial shift. -/
theorem postHeadRaw_join (head : I.Stage) (hhead : head.val = 0)
    (good bad : PolicyRule (I.freshSuffix 1) Seed) (seed : Seed)
    (pre : List (VisibleEvent I)) (hn : VisibleEvent.advanced head ∉ pre)
    (hc : historyCursor (pre ++ [.advanced head]) = 1)
    (after : List (VisibleEvent (I.freshSuffix 1))) :
    postHeadRaw head good bad seed (referenceSuffixHistoryJoin I 1 (pre ++ [.advanced head]) after) =
      referenceSuffixActionLift I 1 (historyActions (pre ++ [.advanced head])).length
        ((if historyWritten (pre ++ [.advanced head]) head = (historyReport (pre ++ [.advanced head]) head).map Prod.fst
          then good else bad) seed after) := by
  have hearly : head.val < 1 := by omega
  have hcursor : historyCursor (referenceSuffixHistoryJoin I 1 (pre ++ [.advanced head]) after) ≠ 0 := by
    rw [historyCursor_referenceSuffixJoin, hc]
    omega
  simp only [postHeadRaw, hcursor, ↓reduceIte, bellmanHeadCut_join head pre hn after,
    historyWritten_referenceSuffixJoin_earlier 1 head hearly,
    historyReport_referenceSuffixJoin_earlier 1 head hearly]
  exact bellmanLiftedAfter_join 1 (pre ++ [.advanced head]) _ seed after

end PaperProofs.Retained.PRetFreshSuffixSelection099
