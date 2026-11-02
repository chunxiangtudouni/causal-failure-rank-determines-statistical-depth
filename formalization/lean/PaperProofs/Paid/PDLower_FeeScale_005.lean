module

public import PaperProofs.Paid.PDLower_Cost_005
public import PaperProofs.Paid.PDLower_FeeScale_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Statistics
open PaperProofs.Statistics.BinarySymmetric

namespace PDLower

universe u

theorem uniformFeeScalePolicyLower (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (fee : ℚ) (hf : 0 ≤ fee) :
    P.UniformFeeScalePolicyLower.{u} C accounting fee hf := by
  intro mode Seed ms
  let : MeasurableSpace Seed := ms
  intro ν hν
  let : IsProbabilityMeasure ν := hν
  intro policy hrisk
  let repairs := meanRepairCount (P.input fee hf) C.val mode accounting policy.rule ν
  let m := P.survivalMassLower
  let p := min (1 / 2) ((repairs + (P.certificate.risk : ℝ)) / m)
  have hm : 0 < m := P.survivalMassLower_pos
  have hd : 0 < (P.certificate.risk : ℝ) := by exact_mod_cast P.certificate.risk_pos
  have hdsmall : (P.certificate.risk : ℝ) ≤ 1 / 64 := by
    have h := (Rat.cast_le (K := ℝ)).mpr P.certificate.risk_le
    norm_num at h
    exact h
  have hN : (1 : ℝ) ≤ P.certificate.stages := by exact_mod_cast (Nat.succ_le_of_lt P.certificate.stages_pos)
  have hr : 0 ≤ repairs := ENNReal.toReal_nonneg
  have hfee : (0 : ℝ) ≤ fee := by exact_mod_cast hf
  have hp : 0 < p := lt_min (by norm_num) (div_pos (add_pos_of_nonneg_of_pos hr hd) hm)
  have hph : p ≤ 1 / 2 := min_le_left _ _
  have hscalar := fee_scalar_original P.a_pos hN hd hdsmall hr hfee
  have husage := usageLower P fee hf C mode accounting Seed ms ν hν policy hrisk
  have hrepair : ENNReal.ofReal repairs = expectedRepairCount (P.input fee hf) C.val mode accounting policy.rule ν :=
    ofReal_meanRepairCount (P.input fee hf) C.val mode accounting policy.rule policy.legal ν
  calc
    P.feeScaleLowerAmount fee ≤ ENNReal.ofReal (P.a * m * phiReal p + (fee : ℝ) * repairs) :=
      ENNReal.ofReal_le_ofReal hscalar
    _ = ENNReal.ofReal (P.a * m) * phi p +
        ENNReal.ofReal (fee : ℝ) * expectedRepairCount (P.input fee hf) C.val mode accounting policy.rule ν := by
      rw [ENNReal.ofReal_add (mul_nonneg (mul_nonneg P.a_pos.le hm.le) (phiReal_nonneg hp hph))
          (mul_nonneg hfee hr),
        ENNReal.ofReal_mul (mul_nonneg P.a_pos.le hm.le), ← phi_of_pos hp,
        ENNReal.ofReal_mul hfee,
        hrepair]
    _ ≤ _ := husage

theorem uniformFeeScaleValueLower (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (fee : ℚ) (hf : 0 ≤ fee) :
    P.UniformFeeScaleValueLower C accounting fee hf := by
  intro mode
  unfold Parameters.paidValue value
  refine le_iInf fun Seed => le_iInf fun ms => ?_
  let : MeasurableSpace Seed := ms
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  exact uniformFeeScalePolicyLower P C accounting fee hf mode Seed ms ν hν policy.val policy.property

end PDLower
