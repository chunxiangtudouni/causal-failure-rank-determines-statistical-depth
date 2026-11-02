module

public import PaperProofs.Paid.PDMenu_CurrentReplayFacts_024
public import PaperProofs.Paid.PDMenu_SuffixActualCharge_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- The independently defined full current-payment value is below every
actual replay under every Dirac seed. The supplied source history is only
public Startup data; no input performance, legality or success oracle occurs. -/
theorem paidPenaltyValue_le_paidReplay_dirac (input : StatisticalInput I) (first : ℕ)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule)
    (startup : Startup I) (seed : Seed) (penalty : ℝ≥0∞) :
    let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools
      (replayedSuffixCandidate first accounting rule startup)
    paidPenaltyValue (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first))
      (zeroNormalAccounting (I.freshSuffix first)) penalty ≤
      ∫⁻ fresh, runPaidPenaltyCharge (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first))
        (zeroNormalAccounting (I.freshSuffix first)) targetRule penalty (seed, fresh)
        ∂(input.freshSuffix first).worldLaw := by
  let targetPolicy := paidReplayedSuffixAvailablePolicy input first accounting rule hm startup
  have hbound := paidPenaltyValue_le_policy_any_seed (input.freshSuffix first)
    (paidRelaxedContract (I.freshSuffix first)) (zeroNormalAccounting (I.freshSuffix first))
    penalty targetPolicy.val (Measure.dirac seed)
  rw [paidPenaltyObjective_eq_lintegral _ _ _ _ targetPolicy.val.measurable_rule] at hbound
  rw [StatisticalInput.seededWorldLaw, Measure.dirac_prod,
    lintegral_map (measurable_runPaidPenaltyCharge _ _ _ _ targetPolicy.val.measurable_rule penalty)
      measurable_prodMk_left] at hbound
  exact hbound

end PDMenu
