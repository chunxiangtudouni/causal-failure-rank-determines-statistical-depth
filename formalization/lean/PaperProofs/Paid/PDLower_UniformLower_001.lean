module

public import PaperProofs.Paid.PDLower_FreeSqueeze_001
public import PaperProofs.Paid.PDLower_Price_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Structure
open PaperProofs.Statistics PaperProofs.Paid

namespace PDLower

/-- The lower half of the original uniform-fee price law is independent
of the calibrated backend and every fixed-script resource qualification.
The single cutoff precedes the original rational delta, fee, caps and
accounting; no risk or quota is changed. The full D36 upper half remains
the separately explicit original D26/D29 obligation. -/
theorem fixedPoolUniformFeeLower (pool : FixedSharedPool) :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 → ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ (delta : ℚ), 0 < delta → delta ≤ 1/64 → (delta : ℝ) < cutoff →
        ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract pool.sharedInstance)
          (_hC : C.IsCurrentPayment) (accounting : NormalAccounting pool.sharedInstance),
          ENNReal.ofReal (1-epsilon)*pool.priceScale delta fee/129 ≤
            pool.nativeValue delta fee hfee C accounting := by
  intro epsilon positiveEpsilon smallEpsilon
  obtain ⟨cutoff,positiveCutoff,lower⟩ :=
    (pool.input 0 (by norm_num)).nativeLowerPriceLaw (pool.tools+1) (fixedPool_rank pool)
      epsilon positiveEpsilon
  refine ⟨cutoff,positiveCutoff,?_⟩
  intro delta positiveDelta smallDelta belowCutoff fee hfee C hC accounting
  have positiveReal : (0:ℝ) < delta := by exact_mod_cast positiveDelta
  have freeLower := lower (delta:ℝ) positiveReal belowCutoff C hC.1 accounting
  rw [fixedPool_coefficient] at freeLower
  have nonnegative : 0 ≤ 1-epsilon := by linarith
  have freeScaleLower : ENNReal.ofReal ((1-epsilon)*pool.structuralScaleReal delta) ≤
      pool.nativeValue delta 0 (by norm_num) C accounting := by
    simpa only [FixedSharedPool.nativeValue,FixedSharedPool.structuralScaleReal,mul_assoc] using freeLower
  rw [ENNReal.ofReal_mul nonnegative] at freeScaleLower
  have factor_le_one : ENNReal.ofReal (1-epsilon) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have perturbed : ENNReal.ofReal (1-epsilon)*pool.priceScale delta fee ≤
      min (pool.nativeValue delta 0 (by norm_num) C accounting + pool.feeScale fee) (pool.saturationScale delta) := by
    unfold FixedSharedPool.priceScale
    rw [mul_min,mul_add]
    exact min_le_min (add_le_add freeScaleLower (mul_le_of_le_one_left' factor_le_one))
      (mul_le_of_le_one_left' factor_le_one)
  have nativeLower : min (pool.nativeValue delta 0 (by norm_num) C accounting + pool.feeScale fee)
      (pool.saturationScale delta)/129 ≤ pool.nativeValue delta fee hfee C accounting :=
    nativeSeparationLower (pool.atRisk delta positiveDelta smallDelta) ⟨C,hC⟩ accounting fee hfee
  exact (ENNReal.div_le_div_right perturbed 129).trans nativeLower

end PDLower
