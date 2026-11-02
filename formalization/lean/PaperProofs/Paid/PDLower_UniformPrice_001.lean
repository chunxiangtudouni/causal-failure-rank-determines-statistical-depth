module

public import PaperProofs.Paid.PDLower_ZeroToolsSaturation_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Structure
open PaperProofs.Statistics PaperProofs.Paid

namespace PDLower

/-- Conditional assembly only: the original native D29 remains an explicit
dependency until its actual calibrated performance theorem is delivered. -/
theorem fixedPoolUniformFeePrice_of_nativeSeparation (pool : FixedSharedPool)
    (separation : ∀ P : PaperProofs.Paid.Parameters, P.NativeSeparationClaims) :
    pool.FixedPoolUniformFeePrice := by
  intro epsilon hepsilon hepsilonOne
  obtain ⟨cutoff, hcutoff, hsqueeze⟩ := freeNativeSqueeze pool epsilon hepsilon hepsilonOne
  refine ⟨cutoff, hcutoff, ?_⟩
  intro delta hdelta hsmall hdeltaCutoff fee hfee C hC accounting qualification
  have hfreeQualification := pool.jointQualification_free delta hdelta hsmall fee hfee
    C hC accounting qualification
  have hpaidQualification := pool.jointQualification_paid delta hdelta hsmall fee hfee
    C hC accounting qualification
  obtain ⟨hfreeLower, hfreeUpper⟩ := hsqueeze delta hdelta hsmall hdeltaCutoff
    C hC accounting hfreeQualification
  have hnonnegLower : 0 ≤ 1 - epsilon := by linarith
  have hnonnegUpper : 0 ≤ 1 + epsilon := by linarith
  rw [ENNReal.ofReal_mul hnonnegLower] at hfreeLower
  rw [ENNReal.ofReal_mul hnonnegUpper] at hfreeUpper
  have hperturb := PaperProofs.Paid.Parameters.minPerturbation epsilon hepsilon.le hepsilonOne
    (pool.nativeValue delta 0 (by norm_num) C accounting) (pool.structuralScale delta)
    (pool.feeScale fee) (pool.saturationScale delta) hfreeLower hfreeUpper
  have hnative := separation (pool.atRisk delta hdelta hsmall) fee hfee ⟨C, hC⟩ accounting
  obtain ⟨hpaidUpper, _hwitness⟩ := hnative.2 hpaidQualification
  have hlower :
      min (pool.nativeValue delta 0 (by norm_num) C accounting + pool.feeScale fee)
        (pool.saturationScale delta) / 129 ≤ pool.nativeValue delta fee hfee C accounting :=
    hnative.1
  have hupper : pool.nativeValue delta fee hfee C accounting ≤
      72 * min (pool.nativeValue delta 0 (by norm_num) C accounting + pool.feeScale fee)
        (pool.saturationScale delta) := hpaidUpper
  constructor
  · exact (ENNReal.div_le_div_right hperturb.1 129).trans hlower
  · calc
      _ ≤ 72 * min (pool.nativeValue delta 0 (by norm_num) C accounting + pool.feeScale fee)
          (pool.saturationScale delta) := hupper
      _ ≤ 72 * (ENNReal.ofReal (1 + epsilon) * pool.priceScale delta fee) :=
        mul_le_mul' le_rfl hperturb.2
      _ = _ := (mul_assoc _ _ _).symm

theorem fixedPoolNativePriceClaims_of_nativeSeparation (pool : FixedSharedPool)
    (separation : ∀ P : PaperProofs.Paid.Parameters, P.NativeSeparationClaims) :
    pool.FixedPoolNativePriceClaims :=
  ⟨fixedPoolUniformFeePrice_of_nativeSeparation pool separation,
    pool.zeroToolsFeeIndependence, zeroToolsStructuralSaturation pool⟩

end PDLower
