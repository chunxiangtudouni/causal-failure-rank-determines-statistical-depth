module

public import PaperProofs.Retained.PRet_FreshLocalPrices_042

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshBellmanBounds077

open Common Common.Native PRetFreshLocalPrices042

variable {I : Instance}

private theorem shifted_bound (E : Statistics.BinaryExperiment) (good bad penalty : ℝ)
    (hgap : 0 ≤ bad - good) (hbad : bad ≤ penalty) :
    good + E.localValueReal (bad - good) ≤ penalty := by
  have hlocal := E.localValueReal_le (bad - good) hgap
  calc
    _ ≤ good + (bad - good) := add_le_add (le_refl good) hlocal
    _ = bad := by rw [add_comm good, sub_add_cancel]
    _ ≤ penalty := hbad
/-- A true zero-review local competitor bounds the shifted Bellman
expression by the original failure penalty. This controls head abandon and
finite-paid nonreturn without inventing an infinite observation charge. -/
theorem shiftedLocal_le_penalty (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (penalty : ℝ) (hp : 0 ≤ penalty) :
    goodPenaltyReal input stage old penalty + (input.experiment stage).localValueReal
      (badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty) ≤ penalty :=
  shifted_bound (input.experiment stage) (goodPenaltyReal input stage old penalty) (badPenaltyReal input stage old penalty) penalty
    (localPrice_bounds input stage old penalty hp).1 (badPenalty_le_penalty input stage old penalty hp)
theorem original_min_eq_shiftedLocal (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (penalty : ℝ) (hp : 0 ≤ penalty) :
    min penalty (goodPenaltyReal input stage old penalty + (input.experiment stage).localValueReal
      (badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty)) =
      goodPenaltyReal input stage old penalty + (input.experiment stage).localValueReal
        (badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty) :=
  min_eq_right (shiftedLocal_le_penalty input stage old penalty hp)

end PaperProofs.Retained.PRetFreshBellmanBounds077


