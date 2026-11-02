module

public import Paid.RootD27Endpoint_Math_001
public import PaperProofs.Paid.PDROC_DataBits_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.EndpointOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits RootD27.Endpoint

/-- A direct bound on the original rational power, including the final
advance. It is linear in the largest exponent, never a bit-size recurrence. -/
def powerBudget (P : Parameters) : ℕ :=
  (P.certificate.M + 3) * (4 * ratEncodingBits P.certificate.gamma + 29)

/-- Intrinsic bound for newly assigned endpoint rationals. Caller cells
which this callee does not write retain the caller's separate bound. -/
def rationalBudget (P : Parameters) : ℕ :=
  8 * powerBudget P + ratEncodingBits P.certificate.gamma +
    ratEncodingBits P.reviewFee + natBits P.certificate.M + 64

theorem rowCast_encodingBits (P : Parameters) (m : ℕ)
    (bound : m ≤ P.certificate.M + 1) :
    ratEncodingBits (m : ℚ) ≤ natBits P.certificate.M + 3 := by
  have monotone := natBits_mono bound
  have successor := natBits_add_le P.certificate.M 1
  have one : natBits 1 = 1 := by norm_num [natBits]
  rw [one] at successor
  rw [ratEncodingBits_natCast_menu]
  omega

theorem power_encodingBits (P : Parameters) (m : ℕ)
    (bound : m ≤ P.certificate.M + 2) :
    ratEncodingBits (powerRecurrence P.certificate.odds m) ≤ powerBudget P := by
  have odds := calibrationOdds_encodingBits_le P
    (ratEncodingBits P.certificate.gamma) (le_refl _)
  change ratEncodingBits P.certificate.odds ≤ _ at odds
  have power := ratEncodingBits_pow_le P.certificate.odds m
  rw [powerRecurrence_eq]
  exact power.trans (Nat.mul_le_mul (by omega) (by omega))

theorem advancePower_encodingBits (P : Parameters) (m : ℕ)
    (bound : m ≤ P.certificate.M + 1) :
    ratEncodingBits (powerRecurrence P.certificate.odds m * P.certificate.odds) ≤
      powerBudget P := by
  change ratEncodingBits (powerRecurrence P.certificate.odds (m + 1)) ≤ _
  exact power_encodingBits P (m + 1) (by omega)

/-- Every rational value assigned by the actual initialization, seven row
commands, cast, and single power advance. Bounds are for original Cell.bits,
so the rational-cell tag is already included. -/
structure RationalBounds (P : Parameters) (m : ℕ) : Prop where
  zero : (Cell.rational 0).bits ≤ rationalBudget P
  one : (Cell.rational 1).bits ≤ rationalBudget P
  two : (Cell.rational 2).bits ≤ rationalBudget P
  gamma : (Cell.rational P.certificate.gamma).bits ≤ rationalBudget P
  fee : (Cell.rational P.reviewFee).bits ≤ rationalBudget P
  rowCast : (Cell.rational (m : ℚ)).bits ≤ rationalBudget P
  twoGamma : (Cell.rational (2 * P.certificate.gamma)).bits ≤ rationalBudget P
  oddsNumerator : (Cell.rational (1 + 2 * P.certificate.gamma)).bits ≤ rationalBudget P
  oddsDenominator : (Cell.rational (1 - 2 * P.certificate.gamma)).bits ≤ rationalBudget P
  odds : (Cell.rational P.certificate.odds).bits ≤ rationalBudget P
  power : (Cell.rational (powerRecurrence P.certificate.odds m)).bits ≤ rationalBudget P
  advancePower :
    (Cell.rational (powerRecurrence P.certificate.odds m * P.certificate.odds)).bits ≤
      rationalBudget P
  powerPlusOne :
    (Cell.rational (1 + powerRecurrence P.certificate.odds m)).bits ≤ rationalBudget P
  error :
    (Cell.rational (1 / (1 + powerRecurrence P.certificate.odds m))).bits ≤ rationalBudget P
  twiceError :
    (Cell.rational (2 * (1 / (1 + powerRecurrence P.certificate.odds m)))).bits ≤
      rationalBudget P
  oneMinusTwiceError :
    (Cell.rational (1 - 2 * (1 / (1 + powerRecurrence P.certificate.odds m)))).bits ≤
      rationalBudget P
  meanNumerator :
    (Cell.rational ((m : ℚ) *
      (1 - 2 * (1 / (1 + powerRecurrence P.certificate.odds m))))).bits ≤ rationalBudget P
  mean :
    (Cell.rational ((m : ℚ) *
      (1 - 2 * (1 / (1 + powerRecurrence P.certificate.odds m))) /
        (2 * P.certificate.gamma))).bits ≤ rationalBudget P
  charge :
    (Cell.rational (P.reviewFee * ((m : ℚ) *
      (1 - 2 * (1 / (1 + powerRecurrence P.certificate.odds m))) /
        (2 * P.certificate.gamma)))).bits ≤ rationalBudget P

/-- The fixed arithmetic DAG is bounded once. In particular, no iteration
of a generic addition bound is used over the endpoint loop. Rational total
division is retained; this numerical lemma needs no nonzero-divisor oracle. -/
theorem rationalBounds (P : Parameters) (m : ℕ)
    (bound : m ≤ P.certificate.M + 1) : RationalBounds P m := by
  let G := ratEncodingBits P.certificate.gamma
  let F := ratEncodingBits P.reviewFee
  let N := natBits P.certificate.M
  let H := powerBudget P
  let power := powerRecurrence P.certificate.odds m
  let error : ℚ := 1 / (1 + power)
  have zero : ratEncodingBits (0 : ℚ) = 3 := by
    norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have one : ratEncodingBits (1 : ℚ) = 3 := by
    norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have two : ratEncodingBits (2 : ℚ) = 4 := by
    norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have scale : 4 * G + 29 ≤ H := by
    change 4 * G + 29 ≤ (P.certificate.M + 3) * (4 * G + 29)
    simpa only [one_mul] using Nat.mul_le_mul_right (4 * G + 29)
      (show 1 ≤ P.certificate.M + 3 by omega)
  have cast : ratEncodingBits (m : ℚ) ≤ N + 3 := rowCast_encodingBits P m bound
  have doubled : ratEncodingBits (2 * P.certificate.gamma) ≤ G + 4 := by
    have actual := ratEncodingBits_mul_le (2 : ℚ) P.certificate.gamma
    rw [two] at actual
    omega
  have numerator : ratEncodingBits (1 + 2 * P.certificate.gamma) ≤ 2 * G + 14 := by
    have actual := ratEncodingBits_add_le (1 : ℚ) (2 * P.certificate.gamma)
    rw [one] at actual
    omega
  have denominator : ratEncodingBits (1 - 2 * P.certificate.gamma) ≤ 2 * G + 14 := by
    have actual := ratEncodingBits_sub_le (1 : ℚ) (2 * P.certificate.gamma)
    rw [one] at actual
    omega
  have odds : ratEncodingBits P.certificate.odds ≤ 4 * G + 28 := by
    exact calibrationOdds_encodingBits_le P G (le_refl _)
  have powerBits : ratEncodingBits power ≤ H := power_encodingBits P m (by omega)
  have advance : ratEncodingBits (power * P.certificate.odds) ≤ H :=
    advancePower_encodingBits P m bound
  have sum : ratEncodingBits (1 + power) ≤ 2 * H + 6 := by
    have actual := ratEncodingBits_add_le (1 : ℚ) power
    rw [one] at actual
    omega
  have reciprocal : ratEncodingBits error ≤ 2 * H + 6 := by
    simpa only [error, one_div, ratEncodingBits_inv] using sum
  have twice : ratEncodingBits (2 * error) ≤ 2 * H + 10 := by
    have actual := ratEncodingBits_mul_le (2 : ℚ) error
    rw [two] at actual
    omega
  have tail : ratEncodingBits (1 - 2 * error) ≤ 4 * H + 26 := by
    have actual := ratEncodingBits_sub_le (1 : ℚ) (2 * error)
    rw [one] at actual
    omega
  have weighted : ratEncodingBits ((m : ℚ) * (1 - 2 * error)) ≤ 4 * H + N + 29 := by
    have actual := ratEncodingBits_mul_le (m : ℚ) (1 - 2 * error)
    omega
  have mean : ratEncodingBits ((m : ℚ) * (1 - 2 * error) / (2 * P.certificate.gamma)) ≤
      4 * H + N + G + 33 := by
    have actual := ratEncodingBits_div_le ((m : ℚ) * (1 - 2 * error))
      (2 * P.certificate.gamma)
    omega
  have charge : ratEncodingBits (P.reviewFee *
      ((m : ℚ) * (1 - 2 * error) / (2 * P.certificate.gamma))) ≤
      4 * H + N + G + F + 33 := by
    have actual := ratEncodingBits_mul_le P.reviewFee
      ((m : ℚ) * (1 - 2 * error) / (2 * P.certificate.gamma))
    omega
  have safe (q : ℚ) (bits : ratEncodingBits q ≤ 4 * H + N + G + F + 40) :
      (Cell.rational q).bits ≤ rationalBudget P := by
    change 1 + ratEncodingBits q ≤ _
    change _ ≤ 8 * H + G + F + N + 64
    omega
  exact ⟨safe 0 (by omega), safe 1 (by omega), safe 2 (by omega),
    safe P.certificate.gamma (by omega), safe P.reviewFee (by omega),
    safe (m : ℚ) (by omega), safe (2 * P.certificate.gamma) (by omega),
    safe (1 + 2 * P.certificate.gamma) (by omega),
    safe (1 - 2 * P.certificate.gamma) (by omega),
    safe P.certificate.odds (by omega), safe power (by omega),
    safe (power * P.certificate.odds) (by omega), safe (1 + power) (by omega),
    safe error (by omega), safe (2 * error) (by omega), safe (1 - 2 * error) (by omega),
    safe ((m : ℚ) * (1 - 2 * error)) (by omega),
    safe ((m : ℚ) * (1 - 2 * error) / (2 * P.certificate.gamma)) (by omega),
    safe (P.reviewFee * ((m : ℚ) * (1 - 2 * error) / (2 * P.certificate.gamma))) (by omega)⟩

theorem RationalBounds.endpointError {P : Parameters} {m : ℕ}
    (bounds : RationalBounds P m) :
    (Cell.rational (P.endpointConstant m).error).bits ≤ rationalBudget P := by
  rw [← endpointFromPower_original P m]
  exact bounds.error

theorem RationalBounds.endpointCharge {P : Parameters} {m : ℕ}
    (bounds : RationalBounds P m) :
    (Cell.rational (P.endpointConstant m).charge).bits ≤ rationalBudget P := by
  rw [← endpointFromPower_original P m]
  exact bounds.charge

end PDROC.EndpointOperands
