module

public import PaperProofs.Retained.PRet_FreshOldObligation_039
public import PaperProofs.Retained.PRet_FreshLocalPrices_042

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshBranchValues084

open Common Common.Native PRetFreshOldObligation039
open scoped ENNReal

variable {I : Instance}

theorem ofReal_freshPenaltyReal (input : StatisticalInput I) (first : ℕ)
    (old : Finset I.Stage) (penalty : ℝ) :
    ENNReal.ofReal (freshPenaltyReal input first old penalty) = freshPenalty input first old (ENNReal.ofReal penalty) :=
  ENNReal.ofReal_toReal (freshPenalty_ne_top input first old ENNReal.ofReal_ne_top)

/-- The bad branch is the SAME original fresh infimum with the true old-H
insertion, even on an immediately unmatchable insertion. The latter is the
already proved original boundary; no actual repair/tool is selected. -/
theorem badPenaltyReal_eq_inserted (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (penalty : ℝ) (hp : 0 ≤ penalty) :
    badPenaltyReal input stage old penalty = freshPenaltyReal input (stage.val + 1) (insert stage old) penalty := by
  classical
  unfold badPenaltyReal
  split_ifs with hm
  · rfl
  · rw [freshPenaltyReal, freshPenalty_unmatchable_old input (stage.val + 1) (insert stage old) hm,
      ENNReal.toReal_ofReal hp]

theorem ofReal_goodPenaltyReal (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (penalty : ℝ) :
    ENNReal.ofReal (goodPenaltyReal input stage old penalty) =
      freshPenalty input (stage.val + 1) old (ENNReal.ofReal penalty) :=
  ofReal_freshPenaltyReal input (stage.val + 1) old penalty

theorem ofReal_badPenaltyReal (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (penalty : ℝ) (hp : 0 ≤ penalty) :
    ENNReal.ofReal (badPenaltyReal input stage old penalty) =
      freshPenalty input (stage.val + 1) (insert stage old) (ENNReal.ofReal penalty) := by
  rw [badPenaltyReal_eq_inserted input stage old penalty hp]
  exact ofReal_freshPenaltyReal input (stage.val + 1) (insert stage old) penalty

end PaperProofs.Retained.PRetFreshBranchValues084
