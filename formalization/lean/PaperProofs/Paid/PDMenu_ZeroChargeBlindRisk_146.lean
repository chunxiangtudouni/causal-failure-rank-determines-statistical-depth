module

public import PaperProofs.Paid.PDMenu_ZeroChargeBlindTable_143
public import PaperProofs.Paid.PDROC_ZeroChargeLower_Binomial_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PDROC.MenuExpected

theorem zeroCharge_halfMean (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal (1/2 : ℝ) * ENNReal.ofReal (a : ℝ) +
      ENNReal.ofReal (1/2 : ℝ) * ENNReal.ofReal (b : ℝ) =
        ENNReal.ofReal (((a+b)/2 : ℚ) : ℝ) := by
  have h := ofReal_weighted_sum (1/2) a b (by norm_num) (by norm_num) ha hb
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, show (1:ℝ)-1/2=1/2 by norm_num] at h
  rw [← h]
  congr 2
  ring

noncomputable def zeroChargeBlindFailureIntegral (P : Parameters) (N K : ℕ) (fee : ℚ) (n k : ℕ) : ℝ≥0∞ :=
  ∫⁻ sample : Tail P n,
    failureValue (menuPathSummary P (zeroChargeBlindTable N K fee) n k sample.1 sample.2)
      ∂menuAnalysisLaw P n

theorem zeroChargeBlind_failure_step (P : Parameters) (N K : ℕ) (fee : ℚ) (n k : ℕ)
    (hn : n+1 ≤ N) (hk : k ≤ K) :
    zeroChargeBlindFailureIntegral P N K fee (n+1) k =
      ENNReal.ofReal (1/2 : ℝ) * zeroChargeBlindFailureIntegral P N K fee n k +
      ENNReal.ofReal (1/2 : ℝ) *
        (∫⁻ sample : Tail P n,
          failureValue (badRecord P (zeroChargeBlindTable N K fee) n k
            (if fee=0 then .repair else .abandon) sample) ∂menuAnalysisLaw P n) := by
  have ha : (Parameters.menuEntryAt (zeroChargeBlindTable N K fee) (n+1) k).action =
      .test 0 (if fee=0 then .repair else .abandon) :=
    congrArg MenuEntry.action (zeroChargeBlindTable_entry N K fee (n+1) k hn hk)
  have h := summary_test_failure_integral P (zeroChargeBlindTable N K fee) n k 0 _ ha
  rw [P.binarySymmetric.endpointError_zero] at h
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, show (1:ℝ)-1/2=1/2 by norm_num] at h
  exact h

theorem zeroChargeBlind_failure_integral (P : Parameters) (N K : ℕ) (fee : ℚ) :
    ∀ n, n ≤ N → ∀ k, k ≤ K →
      zeroChargeBlindFailureIntegral P N K fee n k =
        ENNReal.ofReal (PDROC.ZeroChargeLower.Binomial.tail n (if fee=0 then k else 0) : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro _hn k _hk
      simp [zeroChargeBlindFailureIntegral, menuPathSummary_zero, menuPathFinish, failureValue,
        PDROC.ZeroChargeLower.Binomial.tail_zero]
  | succ n ih =>
      intro hn k hk
      rw [zeroChargeBlind_failure_step P N K fee n k hn hk, ih (by omega) k hk]
      by_cases hf : fee=0
      · subst fee
        simp only [ite_true]
        cases k with
        | zero =>
            have hb : (∫⁻ sample : Tail P n,
                failureValue (badRecord P (zeroChargeBlindTable N K 0) n 0 .repair sample)
                ∂menuAnalysisLaw P n) = ENNReal.ofReal (1:ℝ) := by
              simp [badRecord, menuPathAbandon, failureValue]
            rw [hb, PDROC.ZeroChargeLower.Binomial.tail_succ_zero]
            simpa only [Rat.cast_one] using zeroCharge_halfMean (PDROC.ZeroChargeLower.Binomial.tail n 0) 1
              (PDROC.ZeroChargeLower.Binomial.tail_nonneg n 0) (by norm_num)
        | succ k =>
            have hb : (∫⁻ sample : Tail P n,
                failureValue (badRecord P (zeroChargeBlindTable N K 0) n (k+1) .repair sample)
                ∂menuAnalysisLaw P n) = zeroChargeBlindFailureIntegral P N K 0 n k := by
              apply lintegral_congr
              intro sample
              simp only [badRecord, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
                failureValue]
            rw [hb, ih (by omega) k (by omega)]
            simp only [ite_true]
            rw [zeroCharge_halfMean _ _ (PDROC.ZeroChargeLower.Binomial.tail_nonneg n (k+1))
              (PDROC.ZeroChargeLower.Binomial.tail_nonneg n k),
              PDROC.ZeroChargeLower.Binomial.tail_succ_succ]
      · simp only [hf, ite_false]
        have hb : (∫⁻ sample : Tail P n,
            failureValue (badRecord P (zeroChargeBlindTable N K fee) n k .abandon sample)
            ∂menuAnalysisLaw P n) = ENNReal.ofReal (1:ℝ) := by
          simp [badRecord, menuPathAbandon, failureValue]
        rw [hb, PDROC.ZeroChargeLower.Binomial.tail_succ_zero]
        simpa only [Rat.cast_one] using zeroCharge_halfMean (PDROC.ZeroChargeLower.Binomial.tail n 0) 1
          (PDROC.ZeroChargeLower.Binomial.tail_nonneg n 0) (by norm_num)

end PDMenu
