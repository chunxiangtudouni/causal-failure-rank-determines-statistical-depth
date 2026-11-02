module

public import PaperProofs.Paid.CachedFrontend
public import PaperProofs.Paid.PDROC_EndpointDP_002
public import PaperProofs.Paid.PDROC_DataBits_001
public import PaperProofs.Paid.PDROC_DataBits_Mixture_001
public import Mathlib.Data.Rat.Lemmas

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open scoped BigOperators
open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

/-- Common-denominator closure retains a shared denominator instead of
multiplying it once for every summand. -/
theorem sum_den_dvd {ι : Type*} (s : Finset ι) (f : ι → ℚ) (D : ℕ)
    (h : ∀ i ∈ s, (f i).den ∣ D) : (∑ i ∈ s, f i).den ∣ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (Rat.add_den_dvd_lcm _ _).trans
      (Nat.lcm_dvd (h i (Finset.mem_insert_self _ _))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))))

theorem channelCommonDenominator_pos (P : Parameters) : 0 < P.channelCommonDenominator := by
  exact Nat.mul_pos (by decide) (Rat.den_pos _)

/-- The actual two BSC letters share exactly the proposed public bound D. -/
theorem channel_den_dvd (P : Parameters) (truth : Bool) (letter : Fin 2) :
    (P.experiment.channel truth letter).den ∣ P.channelCommonDenominator := by
  have hhalf : (1 / 2 : ℚ).den ∣ P.channelCommonDenominator := by
    change (1 / 2 : ℚ).den ∣ 2 * P.certificate.gamma.den
    norm_num
  have hgamma : P.certificate.gamma.den ∣ P.channelCommonDenominator := by
    exact dvd_mul_left _ _
  change (if letter.val = (if truth then 1 else 0) then
      (1 / 2 : ℚ) + P.certificate.gamma else 1 / 2 - P.certificate.gamma).den ∣ _
  by_cases h : letter.val = (if truth then 1 else 0)
  · rw [ite_eq_left h]
    exact (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd hhalf hgamma)
  · rw [ite_eq_right h]
    exact (Rat.sub_den_dvd_lcm _ _).trans (Nat.lcm_dvd hhalf hgamma)

/-- Actual Array recurrence, not a replacement rational constructor. -/
theorem endpointWalkDistribution_den_dvd (P : Parameters) (level : ℕ) (truth : Bool)
    (n : ℕ) (target : WalkCell level) :
    (P.walkDistribution level truth n target).den ∣ P.channelCommonDenominator ^ n := by
  induction n generalizing target with
  | zero => rw [PDROC.endpointWalkDistribution_zero]; split_ifs <;> simp
  | succ n ih =>
    let channel : Fin 2 → ℚ := fun letter => P.experiment.channel truth letter
    have hrow : P.walkDistribution level truth (n + 1) target =
        ∑ state : WalkCell level, ∑ letter : Fin 2,
          if walkMove level state letter = target then
            P.walkDistribution level truth n state * channel letter else 0 :=
      PDROC.endpointWalkDistribution_succ P level truth n target
    rw [hrow]
    apply sum_den_dvd
    intro state _hs
    apply sum_den_dvd
    intro letter _hl
    split_ifs
    · have hchannel : (channel letter).den ∣ P.channelCommonDenominator := channel_den_dvd P truth letter
      have hproduct := (Rat.mul_den_dvd (P.walkDistribution level truth n state) (channel letter)).trans
        (Nat.mul_dvd_mul (ih state) hchannel)
      simpa only [pow_succ] using hproduct
    · simp

/-- The terminal fair half-loss is the only additional denominator. -/
theorem cappedError_den_dvd (P : Parameters) (m : ℕ) :
    (P.cappedError m).den ∣ 2 * P.channelCommonDenominator ^ P.certificate.Q := by
  let loss : WalkCell (m + 1) → ℚ := fun state =>
    if state.val < m + 1 then 1 else if state.val = m + 1 then 1 / 2 else 0
  change (∑ state : WalkCell (m + 1),
    P.walkDistribution (m + 1) true P.certificate.Q state * loss state).den ∣ _
  apply sum_den_dvd
  intro state _hs
  have hloss : (loss state).den ∣ 2 := by
    dsimp only [loss]
    split_ifs <;> norm_num
  have hproduct := (Rat.mul_den_dvd (P.walkDistribution (m + 1) true P.certificate.Q state) (loss state)).trans
    (Nat.mul_dvd_mul (endpointWalkDistribution_den_dvd P (m + 1) true P.certificate.Q state) hloss)
  simpa only [Nat.mul_comm] using hproduct

theorem cachedCappedError_den_dvd (P : Parameters) (m : ℕ) :
    (P.cachedCappedError m).den ∣ 2 * P.channelCommonDenominator ^ P.certificate.Q :=
  cappedError_den_dvd P m

theorem cappedError_nonneg (P : Parameters) (m : ℕ) : 0 ≤ P.cappedError m :=
  PDROC.endpointCappedError_nonneg P m

/-- Unit-interval control comes from actual nonnegative mass one, without
assuming bounded-test error, endpoint calibration, or successful paths. -/
theorem cappedError_le_one (P : Parameters) (m : ℕ) : P.cappedError m ≤ 1 := by
  let loss : WalkCell (m + 1) → ℚ := fun state =>
    if state.val < m + 1 then 1 else if state.val = m + 1 then 1 / 2 else 0
  change (∑ state : WalkCell (m + 1),
    P.walkDistribution (m + 1) true P.certificate.Q state * loss state) ≤ 1
  calc
    _ ≤ ∑ state : WalkCell (m + 1), P.walkDistribution (m + 1) true P.certificate.Q state := by
      apply Finset.sum_le_sum
      intro state _hs
      have hloss : loss state ≤ 1 := by dsimp only [loss]; split_ifs <;> norm_num
      exact mul_le_of_le_one_right (PDROC.endpointWalkDistribution_nonneg P (m + 1) true P.certificate.Q state) hloss
    _ = 1 := PDROC.endpointWalkDistribution_sum P (m + 1) true P.certificate.Q

/-- Only the original public ceil formula is used to compare the ideal
endpoint exponent with Q. No D23 risk or performance claim is an input. -/
theorem level_le_original_Q (P : Parameters) (m : ℕ) (hm : m ≤ P.certificate.M) :
    m ≤ P.certificate.Q := by
  have hceil : ((P.certificate.M : ℚ) + 1) / P.certificate.gamma ≤
      (P.certificate.Q : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast P.Q_ge_menu_ceil)
  have hmenu : (P.certificate.M : ℚ) + 1 ≤ P.certificate.gamma * P.certificate.Q := by
    simpa only [mul_comm] using (div_le_iff₀ P.certificate.gamma_pos).mp hceil
  have hg : P.certificate.gamma ≤ (1 : ℚ) := by linarith [P.certificate.gamma_le_quarter]
  have hQ : (0 : ℚ) ≤ P.certificate.Q := Nat.cast_nonneg _
  have hproduct : P.certificate.gamma * (P.certificate.Q : ℚ) ≤ P.certificate.Q :=
    mul_le_of_le_one_left hQ hg
  have hmq : (m : ℚ) ≤ P.certificate.Q := by
    have hM : (m : ℚ) ≤ P.certificate.M := by exact_mod_cast hm
    linarith
  exact_mod_cast hmq

end PDROC.DataBits

namespace PDROC.DataBits

/-- Nonnegative actual mass one controls the stored reduced numerator. -/
theorem cappedError_num_natAbs_le_den (P : Parameters) (m : ℕ) :
    (P.cappedError m).num.natAbs ≤ (P.cappedError m).den :=
  ratNumAbs_le_den _ (cappedError_nonneg P m) (cappedError_le_one P m)

theorem cappedError_numBits_le_denBits (P : Parameters) (m : ℕ) :
    ratNumBits (P.cappedError m) ≤ ratDenBits (P.cappedError m) :=
  natBits_mono (cappedError_num_natAbs_le_den P m)

theorem channelCommonDenominator_bits (P : Parameters) (Lgamma : ℕ)
    (hL : ratEncodingBits P.certificate.gamma ≤ Lgamma) :
    natBits P.channelCommonDenominator ≤ Lgamma + 2 := by
  have hg : natBits P.certificate.gamma.den ≤ Lgamma := by
    unfold ratEncodingBits ratDenBits at hL
    omega
  have htwo : natBits 2 = 2 := by norm_num [natBits]
  change natBits (2 * P.certificate.gamma.den) ≤ _
  have hmul := natBits_mul_le 2 P.certificate.gamma.den
  rw [htwo] at hmul
  omega

theorem cappedError_denBits_le (P : Parameters) (Lgamma : ℕ)
    (hL : ratEncodingBits P.certificate.gamma ≤ Lgamma) (m : ℕ) :
    ratDenBits (P.cappedError m) ≤ 2 * (P.certificate.Q + 1) * (Lgamma + 2) := by
  have hD := channelCommonDenominator_bits P Lgamma hL
  have hpos : 0 < 2 * P.channelCommonDenominator ^ P.certificate.Q :=
    Nat.mul_pos (by decide) (pow_pos (channelCommonDenominator_pos P) _)
  have hbase : ratDenBits (P.cappedError m) ≤
      natBits (2 * P.channelCommonDenominator ^ P.certificate.Q) :=
    ratDenBits_le_of_dvd hpos (cappedError_den_dvd P m)
  have hmul := natBits_mul_le 2 (P.channelCommonDenominator ^ P.certificate.Q)
  have hpow := natBits_pow_le P.channelCommonDenominator P.certificate.Q
  have htwo : natBits 2 = 2 := by norm_num [natBits]
  rw [htwo] at hmul
  have hscale := Nat.mul_le_mul_left P.certificate.Q hD
  nlinarith [Nat.zero_le (P.certificate.Q * (Lgamma + 2))]

theorem cappedError_encodingBits_le (P : Parameters) (Lgamma : ℕ)
    (hL : ratEncodingBits P.certificate.gamma ≤ Lgamma) (m : ℕ) :
    ratEncodingBits (P.cappedError m) ≤ 5 * (P.certificate.Q + 1) * (Lgamma + 2) := by
  have hden := cappedError_denBits_le P Lgamma hL m
  have hnum := cappedError_numBits_le_denBits P m
  have hpos : 0 < (P.certificate.Q + 1) * (Lgamma + 2) := Nat.mul_pos (by omega) (by omega)
  unfold ratEncodingBits
  nlinarith

theorem cachedCappedError_denBits_le (P : Parameters) (Lgamma : ℕ)
    (hL : ratEncodingBits P.certificate.gamma ≤ Lgamma) (m : ℕ) :
    ratDenBits (P.cachedCappedError m) ≤ 2 * (P.certificate.Q + 1) * (Lgamma + 2) :=
  cappedError_denBits_le P Lgamma hL m

theorem cachedCappedError_encodingBits_le (P : Parameters) (Lgamma : ℕ)
    (hL : ratEncodingBits P.certificate.gamma ≤ Lgamma) (m : ℕ) :
    ratEncodingBits (P.cachedCappedError m) ≤ 5 * (P.certificate.Q + 1) * (Lgamma + 2) :=
  cappedError_encodingBits_le P Lgamma hL m

end PDROC.DataBits

namespace PDROC.DataBits

theorem calibrationOdds_encodingBits_le (P : Parameters) (Lgamma : ℕ)
    (hL : ratEncodingBits P.certificate.gamma ≤ Lgamma) :
    ratEncodingBits P.binarySymmetric.odds ≤ 4 * Lgamma + 28 := by
  have hone : ratEncodingBits (1 : ℚ) = 3 := by
    norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have htwo : ratEncodingBits (2 : ℚ) = 4 := by
    norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have hmul := ratEncodingBits_mul_le (2 : ℚ) P.certificate.gamma
  have hplus := ratEncodingBits_add_le (1 : ℚ) (2 * P.certificate.gamma)
  have hminus := ratEncodingBits_sub_le (1 : ℚ) (2 * P.certificate.gamma)
  have hdiv := ratEncodingBits_div_le (1 + 2 * P.certificate.gamma) (1 - 2 * P.certificate.gamma)
  rw [htwo] at hmul
  rw [hone] at hplus hminus
  change ratEncodingBits ((1 + 2 * P.certificate.gamma) / (1 - 2 * P.certificate.gamma)) ≤ _
  omega

/-- The ideal endpoint's stored rational power has linear bit length in
the actual exponent. Original Q already dominates every stored exponent. -/
theorem calibrationEndpoint_encodingBits_le (P : Parameters) (Lgamma : ℕ)
    (hL : ratEncodingBits P.certificate.gamma ≤ Lgamma) (m : ℕ)
    (hm : m ≤ P.certificate.M) :
    ratEncodingBits (P.binarySymmetric.endpointError m) ≤
      40 * (P.certificate.Q + 1) * (Lgamma + 2) := by
  have hodds := calibrationOdds_encodingBits_le P Lgamma hL
  have hpow := ratEncodingBits_pow_le P.binarySymmetric.odds m
  have hadd := ratEncodingBits_add_le (1 : ℚ) (P.binarySymmetric.odds ^ m)
  have hdiv := ratEncodingBits_div_le (1 : ℚ) (1 + P.binarySymmetric.odds ^ m)
  have hone : ratEncodingBits (1 : ℚ) = 3 := by
    norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  rw [hone] at hadd hdiv
  have hmQ := level_le_original_Q P m hm
  have hscale : (m + 1) * (ratEncodingBits P.binarySymmetric.odds + 1) ≤
      (P.certificate.Q + 1) * (4 * Lgamma + 29) :=
    Nat.mul_le_mul (by omega) (by omega)
  change ratEncodingBits (1 / (1 + P.binarySymmetric.odds ^ m)) ≤ _
  nlinarith [Nat.zero_le ((P.certificate.Q + 1) * Lgamma)]

/-- No calibration performance, nonzero divisor, or [0,1] weight premise:
the original total rational division, including denominator zero, is kept. -/
theorem calibrationWeight_encodingBits_le (P : Parameters) (Lgamma : ℕ)
    (hL : ratEncodingBits P.certificate.gamma ≤ Lgamma) (m : ℕ)
    (hm : m ≤ P.certificate.M) :
    ratEncodingBits (P.calibrationWeight m) ≤ 256 * (P.certificate.Q + 1) * (Lgamma + 2) := by
  have he := calibrationEndpoint_encodingBits_le P Lgamma hL m hm
  have hq := cappedError_encodingBits_le P Lgamma hL m
  have hhalf : ratEncodingBits (1 / 2 : ℚ) = 4 := by
    norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have hu := ratEncodingBits_sub_le (1 / 2 : ℚ) (P.binarySymmetric.endpointError m)
  have hv := ratEncodingBits_sub_le (1 / 2 : ℚ) (P.cappedError m)
  have hw := ratEncodingBits_div_le ((1 / 2 : ℚ) - P.binarySymmetric.endpointError m)
    ((1 / 2 : ℚ) - P.cappedError m)
  rw [hhalf] at hu hv
  have hpos : 0 < (P.certificate.Q + 1) * (Lgamma + 2) := Nat.mul_pos (by omega) (by omega)
  change ratEncodingBits (((1 / 2 : ℚ) - P.binarySymmetric.endpointError m) /
    ((1 / 2 : ℚ) - P.cappedError m)) ≤ _
  nlinarith

theorem calibrationWeight_denBits_le (P : Parameters) (Lgamma : ℕ)
    (hL : ratEncodingBits P.certificate.gamma ≤ Lgamma) (m : ℕ)
    (hm : m ≤ P.certificate.M) :
    ratDenBits (P.calibrationWeight m) ≤ 256 * (P.certificate.Q + 1) * (Lgamma + 2) := by
  have he := calibrationWeight_encodingBits_le P Lgamma hL m hm
  unfold ratEncodingBits at he
  omega

theorem calibrationWeight_numBits_le (P : Parameters) (Lgamma : ℕ)
    (hL : ratEncodingBits P.certificate.gamma ≤ Lgamma) (m : ℕ)
    (hm : m ≤ P.certificate.M) :
    ratNumBits (P.calibrationWeight m) ≤ 256 * (P.certificate.Q + 1) * (Lgamma + 2) := by
  have he := calibrationWeight_encodingBits_le P Lgamma hL m hm
  unfold ratEncodingBits at he
  omega

theorem cachedCalibrationWeight_denBits_le (P : Parameters) (Lgamma : ℕ)
    (hL : ratEncodingBits P.certificate.gamma ≤ Lgamma) (m : ℕ)
    (hm : m ≤ P.certificate.M) :
    ratDenBits (P.cachedCalibrationWeight (P.calibrationWeightCache P.endpointCache) m) ≤
      256 * (P.certificate.Q + 1) * (Lgamma + 2) := by
  simpa only [cachedCalibrationWeight_eq] using calibrationWeight_denBits_le P Lgamma hL m hm

theorem cachedCalibrationWeight_encodingBits_le (P : Parameters) (Lgamma : ℕ)
    (hL : ratEncodingBits P.certificate.gamma ≤ Lgamma) (m : ℕ)
    (hm : m ≤ P.certificate.M) :
    ratEncodingBits (P.cachedCalibrationWeight (P.calibrationWeightCache P.endpointCache) m) ≤
      256 * (P.certificate.Q + 1) * (Lgamma + 2) := by
  simpa only [cachedCalibrationWeight_eq] using calibrationWeight_encodingBits_le P Lgamma hL m hm

/-- Exact original universal calibration-data target, with C=256. -/
theorem calibrationBitClaims : PaperProofs.Paid.Parameters.CalibrationBitClaims := by
  refine ⟨256, by decide, ?_⟩
  intro P Lgamma hL m hm
  refine ⟨cachedCappedError_den_dvd P m, ?_,
    cachedCalibrationWeight_denBits_le P Lgamma hL m hm,
    cachedCalibrationWeight_encodingBits_le P Lgamma hL m hm⟩
  have hden := cachedCappedError_denBits_le P Lgamma hL m
  nlinarith [Nat.zero_le ((P.certificate.Q + 1) * (Lgamma + 2))]

end PDROC.DataBits
