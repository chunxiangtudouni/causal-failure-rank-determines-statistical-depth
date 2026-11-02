module

public import PaperProofs.Paid.PDLower_BlindNumeric_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDLower

universe u

theorem blindRepairAmount_nonneg (P : Parameters) :
    0 ≤ (P.certificate.stages : ℝ) / 2 - P.certificate.stages * (P.certificate.risk : ℝ) := by
  have hsmall := (Rat.cast_le (K := ℝ)).mpr P.certificate.risk_le
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hsmall
  have hhalf : (P.certificate.risk : ℝ) ≤ 1 / 2 := by linarith
  have hproduct := mul_le_mul_of_nonneg_left hhalf
    (Nat.cast_nonneg P.certificate.stages : (0 : ℝ) ≤ P.certificate.stages)
  nlinarith only [hproduct]

theorem meanRepairCount_eq_blindAmount (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : Contract P.sharedInstance) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type u} [MeasurableSpace Seed] (rule : PolicyRule P.sharedInstance Seed) (ν : Measure Seed)
    (hcount : expectedRepairCount (P.input fee hf) C mode accounting rule ν =
      ENNReal.ofReal ((P.certificate.stages : ℝ) / 2 - P.certificate.stages * (P.certificate.risk : ℝ))) :
    meanRepairCount (P.input fee hf) C mode accounting rule ν =
      (P.certificate.stages : ℝ) / 2 - P.certificate.stages * (P.certificate.risk : ℝ) := by
  unfold meanRepairCount
  rw [hcount, ENNReal.toReal_ofReal (blindRepairAmount_nonneg P)]

theorem delayedPayment_mean_numeric (P : Parameters) (hN : 6 ≤ P.certificate.stages)
    (fee : ℚ) (hf : 0 ≤ fee) (C : Contract P.sharedInstance) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type u} [MeasurableSpace Seed]
    (rule : PolicyRule P.sharedInstance Seed) (ν : Measure Seed)
    (hcount : expectedRepairCount (P.input fee hf) C mode accounting rule ν =
      ENNReal.ofReal ((P.certificate.stages : ℝ) / 2 - P.certificate.stages * (P.certificate.risk : ℝ))) :
    let repairs := meanRepairCount (P.input fee hf) C mode accounting rule ν
    repairs + (P.certificate.risk : ℝ) <
      P.certificate.stages * (1 - (P.certificate.risk : ℝ)) / 2 ∧
    0 < ENNReal.ofReal (P.a * P.certificate.stages * (1 - (P.certificate.risk : ℝ))) *
      PaperProofs.Statistics.BinarySymmetric.phi (min (1 / 2)
        ((repairs + (P.certificate.risk : ℝ)) /
          ((P.certificate.stages : ℝ) * (1 - (P.certificate.risk : ℝ))))) :=
  delayedPayment_numeric P hN _
    (meanRepairCount_eq_blindAmount P fee hf C mode accounting rule ν hcount)

end PDLower
