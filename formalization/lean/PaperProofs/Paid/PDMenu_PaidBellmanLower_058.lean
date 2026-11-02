module

public import PaperProofs.Paid.PDMenu_PaidShiftedLower_057
public import PaperProofs.Statistics.RootBSCEndpointPenalty001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {Seed : Type*} [MeasurableSpace Seed]

/-- Lower bound for every original whole paid policy, with the exact
endpoint objective. Root's independent original-ROC lemma only consumes
the SAME extracted admissible test; no source performance is assumed. -/
theorem paidEndpointInf_le_policy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (hn : 0 < n) (C : Contract (freshInstance n k)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance n k))
    (policy : Policy (P.freshInput n k fee hfee) C .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty : ℝ≥0∞) (hp : penalty ≠ ⊤) :
    (⨅ m : ℕ, P.paidEndpointObjective fee hfee n k penalty m) ≤
      paidPenaltyObjective (P.freshInput n k fee hfee) C accounting policy.rule ν penalty := by
  let input := P.freshInput n k fee hfee
  let head : (freshInstance n k).Stage := ⟨0, by simpa [freshInstance] using hn⟩
  let good := P.paidGoodSuccessor fee hfee n k penalty
  let bad := P.paidBadSuccessor fee hfee n k penalty
  let gap := bad.toReal - good.toReal
  let test := nativeHeadTest input head policy.rule policy.measurable_rule
  have ho := paidSuccessorOrder P fee hfee n k penalty hn hp
  have hb : bad ≠ ⊤ := ne_top_of_le_ne_top hp ho.2.2
  have hgap : 0 ≤ gap := sub_nonneg.mpr (ENNReal.toReal_mono hb ho.2.1)
  have hstat := RootBSCEndpointPenalty.endpointInf_le_bayesObjective_any_seed P.binarySymmetric ν test gap hgap
  have hInf : (⨅ m : ℕ, P.paidEndpointObjective fee hfee n k penalty m) =
      good + RootBSCEndpointPenalty.endpointInf P.binarySymmetric gap := by
    simp_rw [paidEndpointObjective_eq_shifted P fee hfee n k penalty hn hp]
    exact ENNReal.add_iInf.symm
  calc
    _ = good + RootBSCEndpointPenalty.endpointInf P.binarySymmetric gap := hInf
    _ ≤ good + (input.experiment head).bayesObjective ν test (ENNReal.ofReal gap) := add_le_add le_rfl hstat
    _ ≤ _ := paidFresh_shiftedBayes_lower P fee hfee n k hn C hC accounting policy ν head rfl penalty hp

/-- The independent full-policy infimum retains the original private-seed
comparison class; no scalar recurrence has been inserted into its definition. -/
theorem paidEndpointInf_le_freshPaidPenalty (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k : ℕ) (penalty : ℝ≥0∞) (hn : 0 < n) (hp : penalty ≠ ⊤) :
    (⨅ m : ℕ, P.paidEndpointObjective fee hfee n k penalty m) ≤ P.freshPaidPenalty fee hfee n k penalty := by
  change _ ≤ paidPenaltyValue (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _) penalty
  unfold paidPenaltyValue
  refine le_iInf fun Seed => le_iInf fun m => ?_
  let : MeasurableSpace Seed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  exact paidEndpointInf_le_policy P fee hfee n k hn (paidRelaxedContract _) (paidRelaxedContract_rights _)
    (zeroAccounting _) policy ν penalty hp

theorem freshPaidPenalty_bellman_lower (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k : ℕ) (penalty : ℝ≥0∞) (hn : 0 < n) (hp : penalty ≠ ⊤) :
    min penalty (⨅ m : ℕ, P.paidEndpointObjective fee hfee n k penalty m) ≤ P.freshPaidPenalty fee hfee n k penalty :=
  (min_le_right _ _).trans (paidEndpointInf_le_freshPaidPenalty P fee hfee n k penalty hn hp)

end PDMenu

