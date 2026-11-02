module

public import PaperProofs.Paid.PDMenu_PaidAllPolicyLower_056
public import PaperProofs.Paid.PDMenu_PaidUpperAlgebra_042
public import PaperProofs.Paid.PDMenu_PaidSuccessorOrder_028
public import PaperProofs.Common.NativeHeadBayes

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {Seed : Type*} [MeasurableSpace Seed]

/-- The genuine arbitrary-policy paid lower bound expressed through its
same extracted, possibly non-MAP, head test and the real successor gap. -/
theorem paidFresh_shiftedBayes_lower (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (hn : 0 < n) (C : Contract (freshInstance n k)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance n k))
    (policy : Policy (P.freshInput n k fee hfee) C .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head : (freshInstance n k).Stage) (hhead : head.val = 0) (penalty : ℝ≥0∞) (hp : penalty ≠ ⊤) :
    let input := P.freshInput n k fee hfee
    P.paidGoodSuccessor fee hfee n k penalty +
      (input.experiment head).bayesObjective ν (nativeHeadTest input head policy.rule policy.measurable_rule)
        (ENNReal.ofReal ((P.paidBadSuccessor fee hfee n k penalty).toReal -
          (P.paidGoodSuccessor fee hfee n k penalty).toReal)) ≤
      paidPenaltyObjective input C accounting policy.rule ν penalty := by
  intro input
  let good := P.paidGoodSuccessor fee hfee n k penalty
  let bad := P.paidBadSuccessor fee hfee n k penalty
  have ho := paidSuccessorOrder P fee hfee n k penalty hn hp
  have hb : bad ≠ ⊤ := ne_top_of_le_ne_top hp ho.2.2
  have hg : good ≠ ⊤ := ne_top_of_le_ne_top hb ho.2.1
  have hGood : ENNReal.ofReal good.toReal = good := ENNReal.ofReal_toReal hg
  have hBad : ENNReal.ofReal bad.toReal = bad := ENNReal.ofReal_toReal hb
  have hShift := shiftedBayesObjective_eq_seededWorld_integral input head ν
    (nativeHeadTest input head policy.rule policy.measurable_rule) good.toReal bad.toReal
    ENNReal.toReal_nonneg (ENNReal.toReal_mono hb ho.2.1)
  rw [hGood, hBad] at hShift
  calc
    _ = ∫⁻ sample, (input.experiment head).observationCharge
          (headExitStop input head policy.rule sample.1 (worldTapes input sample.2 head)) +
        paidHeadContinuationWeight input head policy.rule good bad sample ∂input.seededWorldLaw ν := by
      apply hShift.trans
      apply lintegral_congr
      intro sample
      rfl
    _ ≤ _ := paidFresh_allPolicy_local_lower P fee hfee n k hn C hC accounting policy ν head hhead penalty

/-- Exact endpoint algebra, retaining the independently defined paid
successors and all original finite multipliers. No infinity is subtracted. -/
theorem paidEndpointObjective_eq_shifted (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k : ℕ) (penalty : ℝ≥0∞) (hn : 0 < n) (hp : penalty ≠ ⊤) (m : ℕ) :
    P.paidEndpointObjective fee hfee n k penalty m =
      P.paidGoodSuccessor fee hfee n k penalty +
        (ENNReal.ofReal (P.binarySymmetric.endpointCharge m : ℝ) +
          ENNReal.ofReal ((P.paidBadSuccessor fee hfee n k penalty).toReal -
            (P.paidGoodSuccessor fee hfee n k penalty).toReal) *
          ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ)) := by
  let head : (freshInstance n k).Stage := ⟨0, by simpa [freshInstance] using hn⟩
  let good := P.paidGoodSuccessor fee hfee n k penalty
  let bad := P.paidBadSuccessor fee hfee n k penalty
  let correct := ENNReal.ofReal (1 - (P.binarySymmetric.endpointError m : ℝ))
  let wrong := ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ)
  let charge := ENNReal.ofReal (P.binarySymmetric.endpointCharge m : ℝ)
  let gap := ENNReal.ofReal (bad.toReal - good.toReal)
  have ho := paidSuccessorOrder P fee hfee n k penalty hn hp
  have hb : bad ≠ ⊤ := ne_top_of_le_ne_top hp ho.2.2
  have hg : good ≠ ⊤ := ne_top_of_le_ne_top hb ho.2.1
  have hgap : 0 ≤ bad.toReal - good.toReal := sub_nonneg.mpr (ENNReal.toReal_mono hb ho.2.1)
  have hsplit : bad = good + gap := by
    calc
      bad = ENNReal.ofReal bad.toReal := (ENNReal.ofReal_toReal hb).symm
      _ = ENNReal.ofReal (good.toReal + (bad.toReal - good.toReal)) := by congr 1; ring
      _ = ENNReal.ofReal good.toReal + gap := ENNReal.ofReal_add ENNReal.toReal_nonneg hgap
      _ = good + gap := by rw [ENNReal.ofReal_toReal hg]
  have hweights : correct + wrong = 1 := freshEndpoint_weights_sum P n k fee hfee head m
  change charge + correct * good + wrong * bad = good + (charge + gap * wrong)
  rw [hsplit]
  calc
    _ = charge + (correct + wrong) * good + wrong * gap := by ring
    _ = _ := by rw [hweights, one_mul]; ring

end PDMenu
