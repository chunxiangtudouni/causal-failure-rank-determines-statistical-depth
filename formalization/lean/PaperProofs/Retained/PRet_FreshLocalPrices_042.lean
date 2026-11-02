module

public import PaperProofs.Retained.PRet_FreshOldMonotonicity_041

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshLocalPrices042

open Common Common.Native
open scoped ENNReal
open PRetFreshOldMonotonicity041

variable {I : Instance}

theorem freshPenaltyReal_le_penalty (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (penalty : ℝ) (hp : 0 ≤ penalty) : freshPenaltyReal input next old penalty ≤ penalty := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (freshPenalty_le_penalty input next old (ENNReal.ofReal penalty))
  simpa only [freshPenaltyReal, ENNReal.toReal_ofReal hp] using h

theorem freshPenaltyReal_mono_old (input : StatisticalInput I) (next : ℕ)
    (small large : Finset I.Stage) (hsub : small ⊆ large) (penalty : ℝ) :
    freshPenaltyReal input next small penalty ≤ freshPenaltyReal input next large penalty :=
  ENNReal.toReal_mono (freshPenalty_ne_top input next large ENNReal.ofReal_ne_top)
    (freshPenalty_mono_old input next small large hsub (ENNReal.ofReal penalty))

theorem goodPenalty_nonneg (input : StatisticalInput I) (stage : I.Stage) (old : Finset I.Stage) (penalty : ℝ) :
    0 ≤ goodPenaltyReal input stage old penalty := ENNReal.toReal_nonneg

/-- The two REAL retained continuation prices, with old H retained in both
branches, are ordered before a local test is invoked. -/
theorem goodPenalty_le_badPenalty (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (penalty : ℝ) (hp : 0 ≤ penalty) :
    goodPenaltyReal input stage old penalty ≤ badPenaltyReal input stage old penalty := by
  unfold goodPenaltyReal badPenaltyReal
  split_ifs
  · exact freshPenaltyReal_mono_old input (stage.val + 1) old (insert stage old) (Finset.subset_insert stage old) penalty
  · exact freshPenaltyReal_le_penalty input (stage.val + 1) old penalty hp

theorem badPenalty_le_penalty (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (penalty : ℝ) (hp : 0 ≤ penalty) :
    badPenaltyReal input stage old penalty ≤ penalty := by
  unfold badPenaltyReal
  split_ifs
  · exact freshPenaltyReal_le_penalty input (stage.val + 1) (insert stage old) penalty hp
  · exact le_rfl

theorem localPrice_bounds (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (penalty : ℝ) (hp : 0 ≤ penalty) :
    0 ≤ badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty ∧
      badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty ≤ penalty := by
  refine ⟨sub_nonneg.mpr (goodPenalty_le_badPenalty input stage old penalty hp), ?_⟩
  have h := sub_le_sub (badPenalty_le_penalty input stage old penalty hp)
    (goodPenalty_nonneg input stage old penalty)
  simpa only [sub_zero] using h

end PaperProofs.Retained.PRetFreshLocalPrices042
