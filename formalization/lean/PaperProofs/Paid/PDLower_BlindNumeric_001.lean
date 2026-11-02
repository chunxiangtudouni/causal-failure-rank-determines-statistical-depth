module

public import PaperProofs.Paid.BridgeClaims
public import PaperProofs.Statistics.BSCInformation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics PaperProofs.Paid

namespace PDLower

theorem phi_pos_below_half {error : ℝ} (herror : 0 < error) (hhalf : error < 1 / 2) :
    0 < BinarySymmetric.phi error := by
  rw [BinarySymmetric.phi_of_pos herror]
  apply ENNReal.ofReal_pos.mpr
  have hstrict := BinarySymmetric.phiReal_strictAntiOn
    (show error ∈ Set.Ioc 0 (1 / 2) from ⟨herror, hhalf.le⟩)
    (show (1 / 2 : ℝ) ∈ Set.Ioc 0 (1 / 2) from ⟨by norm_num, le_rfl⟩) hhalf
  simpa only [BinarySymmetric.phiReal_half] using hstrict

theorem delayedPayment_numeric (P : Parameters) (hstages : 6 ≤ P.certificate.stages)
    (repairs : ℝ)
    (hrepairs : repairs = (P.certificate.stages : ℝ) / 2 -
      P.certificate.stages * (P.certificate.risk : ℝ)) :
    repairs + (P.certificate.risk : ℝ) <
      P.certificate.stages * (1 - (P.certificate.risk : ℝ)) / 2 ∧
    0 < ENNReal.ofReal (P.a * P.certificate.stages * (1 - (P.certificate.risk : ℝ))) *
      BinarySymmetric.phi (min (1 / 2)
        ((repairs + (P.certificate.risk : ℝ)) /
          ((P.certificate.stages : ℝ) * (1 - (P.certificate.risk : ℝ))))) := by
  have hN : (6 : ℝ) ≤ P.certificate.stages := by exact_mod_cast hstages
  have hNpositive : (0 : ℝ) < P.certificate.stages := by exact_mod_cast P.certificate.stages_pos
  have hrisk : (0 : ℝ) < P.certificate.risk := by exact_mod_cast P.certificate.risk_pos
  have hsmallCast := (Rat.cast_le (K := ℝ)).mpr P.certificate.risk_le
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hsmallCast
  have hhalf : (P.certificate.risk : ℝ) < 1 / 2 := by linarith
  have hmass : 0 < (P.certificate.stages : ℝ) * (1 - (P.certificate.risk : ℝ)) :=
    mul_pos hNpositive (by linarith)
  have hrepairsPositive : 0 < repairs := by
    have hp := mul_pos hNpositive (sub_pos.mpr hhalf)
    nlinarith only [hrepairs, hp]
  have hgap := mul_pos (show 0 < (P.certificate.stages : ℝ) - 2 by linarith) hrisk
  have hstrict : repairs + (P.certificate.risk : ℝ) <
      P.certificate.stages * (1 - (P.certificate.risk : ℝ)) / 2 := by
    nlinarith only [hrepairs, hgap]
  have hratio : 0 < (repairs + (P.certificate.risk : ℝ)) /
      ((P.certificate.stages : ℝ) * (1 - (P.certificate.risk : ℝ))) :=
    div_pos (add_pos hrepairsPositive hrisk) hmass
  have hratioHalf : (repairs + (P.certificate.risk : ℝ)) /
      ((P.certificate.stages : ℝ) * (1 - (P.certificate.risk : ℝ))) < 1 / 2 := by
    apply (div_lt_iff₀ hmass).mpr
    nlinarith only [hstrict]
  refine ⟨hstrict, ?_⟩
  rw [min_eq_right hratioHalf.le]
  exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (by
    simpa only [mul_assoc] using mul_pos P.a_pos hmass), phi_pos_below_half hratio hratioHalf⟩

end PDLower
