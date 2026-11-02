module

public import PaperProofs.Retained.PRet_FreshLocalPrices_042
public import PaperProofs.Statistics.PenaltyScales

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshCancellation070

open Common Common.Native Statistics PRetFreshLocalPrices042 Filter Asymptotics
open scoped Topology

variable {I : Instance}

/-- Only the bad child's leading term is consumed. This interface is
intended for the STRICTLY shorter-suffix induction, never an assumption of
the current/global fresh penalty asymptotic or a lower bound on the gap. -/
theorem localTerm_tendsto_zero_of_bad_leading (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (depth : ℕ) (B : ℝ) (hB : 0 < B)
    (hbad : Tendsto (fun penalty : ℝ => badPenaltyReal input stage old penalty / iteratedLog depth penalty)
      atTop (𝓝 B)) :
    Tendsto (fun penalty : ℝ => (input.experiment stage).localValueReal
      (badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty) /
        iteratedLog depth penalty) atTop (𝓝 0) := by
  apply (input.experiment stage).localValue_iteratedLog_difference_negligible
    (goodPenaltyReal input stage old) (badPenaltyReal input stage old) depth B hB hbad
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with penalty hp
  exact ⟨goodPenalty_nonneg input stage old penalty, goodPenalty_le_badPenalty input stage old penalty hp⟩

theorem localTerm_isLittleO_of_bad_leading (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (depth : ℕ) (B : ℝ) (hB : 0 < B)
    (hbad : Tendsto (fun penalty : ℝ => badPenaltyReal input stage old penalty / iteratedLog depth penalty)
      atTop (𝓝 B)) :
    (fun penalty : ℝ => (input.experiment stage).localValueReal
      (badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty)) =o[atTop] iteratedLog depth := by
  apply (isLittleO_iff_tendsto' ?_).mpr (localTerm_tendsto_zero_of_bad_leading input stage old depth B hB hbad)
  filter_upwards [(iteratedLog_tendsto_atTop depth).eventually_ne_atTop 0] with penalty hp hzero
  exact (hp hzero).elim

end PaperProofs.Retained.PRetFreshCancellation070
