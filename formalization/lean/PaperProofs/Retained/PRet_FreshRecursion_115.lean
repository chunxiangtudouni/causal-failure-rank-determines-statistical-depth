module

public import PaperProofs.Retained.PRet_FreshBellmanLower_093
public import PaperProofs.Retained.PRet_FreshBellmanUpper_114

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshRecursion115

open Common Common.Native PRetFreshLocalPrices042 PRetFreshBellmanBounds077 PRetFreshBellmanLower093 PRetFreshBellmanUpper114
open scoped ENNReal

variable {I : Instance}

theorem freshPenaltyReal_upper (input : StatisticalInput I) (stage : I.Stage) (old : Finset I.Stage)
    (penalty : ℝ) (hp : 0 ≤ penalty) :
    freshPenaltyReal input stage.val old penalty ≤
      goodPenaltyReal input stage old penalty + (input.experiment stage).localValueReal
        (badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty) := by
  have hn := add_nonneg (goodPenalty_nonneg input stage old penalty)
    ((input.experiment stage).localValueReal_nonneg (badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty))
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (freshPenalty_upper input stage old penalty hp)
  simpa only [freshPenaltyReal, ENNReal.toReal_ofReal hn] using h

/-- EXACT ORIGINAL R04 Bellman recursion for the independently defined
full-policy F value, with true old-H debt, arbitrary private randomness,
partial/nonreturn paths, actual paid observations and no attained optimizer. -/
theorem freshPenaltyRecursion (input : StatisticalInput I) : FreshPenaltyRecursion input := by
  intro stage old hhealthy penalty hp
  rw [original_min_eq_shiftedLocal input stage old penalty hp.le]
  exact le_antisymm (freshPenaltyReal_upper input stage old penalty hp.le)
    (freshPenaltyReal_lower input stage old hhealthy penalty hp.le)

end PaperProofs.Retained.PRetFreshRecursion115
