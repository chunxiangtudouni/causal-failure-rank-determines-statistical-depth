module

public import PaperProofs.Paid.MultiplierSearch
public import PaperProofs.Paid.PenaltyProgram
public import PaperProofs.Common.NativeRelaxation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open scoped ENNReal

namespace PDROC.ZeroChargeLower.Transport

universe u

theorem firstChargeFloor_pos (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    0 < P.firstChargeFloor fee := by
  by_cases zero : fee = 0
  · simpa only [Parameters.firstChargeFloor, zero, ite_true] using P.reviewFee_pos
  · have positive : 0 < fee := lt_of_le_of_ne hfee (Ne.symm zero)
    simpa only [Parameters.firstChargeFloor, zero, ite_false] using
      lt_min P.reviewFee_pos positive

theorem firstChargeFloor_le_reviewFee (P : Parameters) (fee : ℚ) :
    P.firstChargeFloor fee ≤ P.reviewFee := by
  unfold Parameters.firstChargeFloor
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem firstChargeFloor_le_fee (P : Parameters) (fee : ℚ) (positive : 0 < fee) :
    P.firstChargeFloor fee ≤ fee := by
  rw [Parameters.firstChargeFloor, ite_eq_right (ne_of_gt positive)]
  exact min_le_right _ _

theorem positiveValueFloor_pos (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (gap : P.certificate.risk < P.zeroChargeRisk fee) :
    0 < P.positiveValueFloor fee :=
  mul_pos (firstChargeFloor_pos P fee hfee) (sub_pos.mpr gap)

/-- Conditional assembly only: the genuine independently-defined small
penalty value is an explicit intermediate dependency. The final D22 callers
must instantiate this argument with a proved identity. Arbitrary private Seed
universes and the complete original failed/nonreturn bills are retained. -/
theorem smallPenalty_policy_weakDuality (P : Parameters)
    (smallPenaltyValue : ∀ (fee : ℚ) (hfee : 0 ≤ fee),
      P.freshPaidPenalty fee hfee P.certificate.stages P.tools
        (ENNReal.ofReal (P.firstChargeFloor fee : ℝ)) =
        ENNReal.ofReal ((P.firstChargeFloor fee * P.zeroChargeRisk fee : ℚ) : ℝ))
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (mode : ResourceMode)
    {Seed : Type u} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : Policy (P.input fee hfee) C.val mode accounting Seed) :
    ENNReal.ofReal ((P.firstChargeFloor fee * P.zeroChargeRisk fee : ℚ) : ℝ) ≤
      expectedBill (P.input fee hfee) C.val mode accounting policy.rule ν +
        ENNReal.ofReal (P.firstChargeFloor fee : ℝ) *
          risk (P.input fee hfee) C.val mode accounting policy.rule ν := by
  cases mode with
  | uncapped =>
    have bound := paidPenaltyValue_le_policy_any_seed (P.input fee hfee) C.val accounting
      (ENNReal.ofReal (P.firstChargeFloor fee : ℝ)) policy ν
    rw [← P.freshPaidPenaltyOriginalIdentification fee hfee C accounting
      (ENNReal.ofReal (P.firstChargeFloor fee : ℝ)), smallPenaltyValue fee hfee] at bound
    exact bound
  | native =>
    let relaxed := Policy.relax (P.input fee hfee) C.val accounting policy
    have bound := paidPenaltyValue_le_policy_any_seed (P.input fee hfee) C.val accounting
      (ENNReal.ofReal (P.firstChargeFloor fee : ℝ)) relaxed ν
    rw [← P.freshPaidPenaltyOriginalIdentification fee hfee C accounting
      (ENNReal.ofReal (P.firstChargeFloor fee : ℝ)), smallPenaltyValue fee hfee] at bound
    change _ ≤ expectedBill (P.input fee hfee) C.val .uncapped accounting policy.rule ν +
      ENNReal.ofReal (P.firstChargeFloor fee : ℝ) *
        risk (P.input fee hfee) C.val .uncapped accounting policy.rule ν at bound
    rwa [expectedBill_uncapped_eq_native (P.input fee hfee) C.val accounting policy.rule policy.legal ν,
      risk_uncapped_eq_native (P.input fee hfee) C.val accounting policy.rule policy.legal ν] at bound

/-- Exact original zero-bill lower field, conditional only on the displayed
independent small-penalty value identity. -/
theorem originalZeroChargePolicyLower_of_smallPenaltyValue (P : Parameters)
    (smallPenaltyValue : ∀ (fee : ℚ) (hfee : 0 ≤ fee),
      P.freshPaidPenalty fee hfee P.certificate.stages P.tools
        (ENNReal.ofReal (P.firstChargeFloor fee : ℝ)) =
        ENNReal.ofReal ((P.firstChargeFloor fee * P.zeroChargeRisk fee : ℚ) : ℝ)) :
    ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
      (accounting : NormalAccounting P.sharedInstance)
      (mode : ResourceMode) (Seed : Type u) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
        letI : IsProbabilityMeasure ν := hν
        ∀ policy : Policy (P.input fee hfee) C.val mode accounting Seed,
          expectedBill (P.input fee hfee) C.val mode accounting policy.rule ν = 0 →
            ENNReal.ofReal (P.zeroChargeRisk fee : ℝ) ≤
              risk (P.input fee hfee) C.val mode accounting policy.rule ν := by
  intro fee hfee C accounting mode Seed m
  let : MeasurableSpace Seed := m
  intro ν hν
  let : IsProbabilityMeasure ν := hν
  intro policy zeroBill
  have bound := smallPenalty_policy_weakDuality P smallPenaltyValue fee hfee C accounting mode ν policy
  have positive : 0 < (P.firstChargeFloor fee : ℝ) := by
    exact_mod_cast firstChargeFloor_pos P fee hfee
  rw [zeroBill, zero_add, Rat.cast_mul, ENNReal.ofReal_mul positive.le] at bound
  exact (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr positive))
    ENNReal.ofReal_ne_top).mp bound

/-- Exact original positive cost lower field. ENNReal subtraction retains
infinite expected bills, and no finite-cost or return premise is introduced. -/
theorem originalPositiveCostFloor_of_smallPenaltyValue (P : Parameters)
    (smallPenaltyValue : ∀ (fee : ℚ) (hfee : 0 ≤ fee),
      P.freshPaidPenalty fee hfee P.certificate.stages P.tools
        (ENNReal.ofReal (P.firstChargeFloor fee : ℝ)) =
        ENNReal.ofReal ((P.firstChargeFloor fee * P.zeroChargeRisk fee : ℚ) : ℝ)) :
    ∀ (fee : ℚ) (hfee : 0 ≤ fee), P.certificate.risk < P.zeroChargeRisk fee →
      ∀ (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
        (mode : ResourceMode) (Seed : Type u) (m : MeasurableSpace Seed),
        letI : MeasurableSpace Seed := m
        ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
          letI : IsProbabilityMeasure ν := hν
          ∀ policy : Policy (P.input fee hfee) C.val mode accounting Seed,
            risk (P.input fee hfee) C.val mode accounting policy.rule ν ≤ P.targetRisk →
              ENNReal.ofReal (P.positiveValueFloor fee : ℝ) ≤
                expectedBill (P.input fee hfee) C.val mode accounting policy.rule ν := by
  intro fee hfee _gap C accounting mode Seed m
  let : MeasurableSpace Seed := m
  intro ν hν
  let : IsProbabilityMeasure ν := hν
  intro policy riskBound
  have positive : 0 < (P.firstChargeFloor fee : ℝ) := by
    exact_mod_cast firstChargeFloor_pos P fee hfee
  have riskNonneg : (0 : ℝ) ≤ P.certificate.risk := by
    exact_mod_cast P.certificate.risk_pos.le
  have bound := smallPenalty_policy_weakDuality P smallPenaltyValue fee hfee C accounting mode ν policy
  have upper : ENNReal.ofReal (P.firstChargeFloor fee : ℝ) *
      risk (P.input fee hfee) C.val mode accounting policy.rule ν ≤
      ENNReal.ofReal (P.firstChargeFloor fee : ℝ) * P.targetRisk := by
    simpa only [mul_comm] using
      mul_le_mul_left riskBound (ENNReal.ofReal (P.firstChargeFloor fee : ℝ))
  have total := bound.trans (add_le_add le_rfl upper)
  have priceRisk : ENNReal.ofReal (P.firstChargeFloor fee : ℝ) * P.targetRisk =
      ENNReal.ofReal ((P.firstChargeFloor fee * P.certificate.risk : ℚ) : ℝ) := by
    rw [Parameters.targetRisk, Rat.cast_mul, ENNReal.ofReal_mul positive.le]
  rw [priceRisk] at total
  have difference := tsub_le_iff_right.mpr total
  have exactDifference : ENNReal.ofReal (P.positiveValueFloor fee : ℝ) =
      ENNReal.ofReal ((P.firstChargeFloor fee * P.zeroChargeRisk fee : ℚ) : ℝ) -
        ENNReal.ofReal ((P.firstChargeFloor fee * P.certificate.risk : ℚ) : ℝ) := by
    rw [Parameters.positiveValueFloor, Rat.cast_mul, Rat.cast_sub, mul_sub,
      ENNReal.ofReal_sub _ (mul_nonneg positive.le riskNonneg)]
    simp only [Rat.cast_mul]
  rw [exactDifference]
  exact difference

end PDROC.ZeroChargeLower.Transport
