module

public import PaperProofs.Paid.CachedFrontend

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators
open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

theorem rat_den_sum_dvd {ι : Type*} (s : Finset ι) (f : ι → ℚ) (D : ℕ)
    (h : ∀ i ∈ s, (f i).den ∣ D) : (∑ i ∈ s, f i).den ∣ D := by
  classical
  suffices hall : ∀ t : Finset ι, (∀ i ∈ t, (f i).den ∣ D) →
      (∑ i ∈ t, f i).den ∣ D from hall s h
  intro t
  induction t using Finset.induction_on with
  | empty => intro _; simp
  | @insert a t ha ih =>
    intro ht
    rw [Finset.sum_insert ha]
    exact (Rat.add_den_dvd_lcm _ _).trans
      (Nat.lcm_dvd (ht a (by simp)) (ih (fun i hi => ht i (by simp [hi]))))

theorem zeroChargeRisk_den_dvd (P : Parameters) (fee : ℚ) :
    (P.zeroChargeRisk fee).den ∣ 2 ^ P.certificate.stages := by
  have hhalf : ((1 / 2 : ℚ) ^ P.certificate.stages).den = 2 ^ P.certificate.stages := by
    rw [Rat.den_pow]
    norm_num
  unfold PaperProofs.Paid.Parameters.zeroChargeRisk
  split_ifs
  · unfold PaperProofs.Paid.Parameters.blindBinomialTail
    apply rat_den_sum_dvd
    intro mistakes _hm
    split_ifs
    · simpa only [Rat.den_natCast, one_mul, hhalf] using
        Rat.mul_den_dvd (Nat.choose P.certificate.stages mistakes : ℚ)
          ((1 / 2 : ℚ) ^ P.certificate.stages)
    · simp
  · simpa only [Rat.ofNat_sub_den, hhalf] using dvd_refl (2 ^ P.certificate.stages)

theorem rat_one_div_den_le (q : ℚ) (hq : 0 < q) : 1 / (q.den : ℚ) ≤ q := by
  have hn : (1 : ℤ) ≤ q.num := by have := Rat.num_pos.mpr hq; omega
  have hnq : (1 : ℚ) ≤ (q.num : ℚ) := by exact_mod_cast hn
  calc
    1 / (q.den : ℚ) ≤ (q.num : ℚ) / (q.den : ℚ) :=
      div_le_div_of_nonneg_right hnq (by exact_mod_cast q.den_pos.le)
    _ = q := Rat.num_div_den q

theorem rat_positive_gap_lower (z r : ℚ) (D : ℕ) (hD : 0 < D)
    (hz : z.den ∣ D) (hgap : r < z) :
    1 / ((D : ℚ) * (r.den : ℚ)) ≤ z - r := by
  have hden : (z - r).den ∣ D * r.den :=
    (Rat.sub_den_dvd _ _).trans (Nat.mul_dvd_mul hz dvd_rfl)
  have hle : (z - r).den ≤ D * r.den :=
    Nat.le_of_dvd (Nat.mul_pos hD r.den_pos) hden
  have hcast : ((z - r).den : ℚ) ≤ (D : ℚ) * (r.den : ℚ) := by exact_mod_cast hle
  exact (one_div_le_one_div_of_le (by exact_mod_cast (z - r).den_pos) hcast).trans
    (rat_one_div_den_le (z - r) (sub_pos.mpr hgap))

theorem firstChargeFloor_encoding (P : Parameters) (fee : ℚ) :
    ratEncodingBits (P.firstChargeFloor fee) ≤ ratEncodingBits P.reviewFee + ratEncodingBits fee := by
  unfold PaperProofs.Paid.Parameters.firstChargeFloor
  split_ifs
  · exact Nat.le_add_right _ _
  · rcases le_total P.reviewFee fee with h | h
    · rw [min_eq_left h]
      exact Nat.le_add_right _ _
    · rw [min_eq_right h]
      exact Nat.le_add_left _ _

theorem positiveGapBitClaims (P : Parameters) : P.PositiveGapBitClaims := by
  intro fee _hfee
  refine ⟨firstChargeFloor_encoding P fee, ?_⟩
  intro hgap
  have hlower := rat_positive_gap_lower (P.zeroChargeRisk fee) P.certificate.risk
    (2 ^ P.certificate.stages) (by positivity) (zeroChargeRisk_den_dvd P fee) hgap
  have hlower' : 1 / ((2 : ℚ) ^ P.certificate.stages * (P.certificate.risk.den : ℚ)) ≤
      P.zeroChargeRisk fee - P.certificate.risk := by exact_mod_cast hlower
  refine ⟨hlower', ?_⟩
  have hδ : 0 < (P.certificate.risk.den : ℝ) := by exact_mod_cast P.certificate.risk.den_pos
  have hD : 0 < (2 : ℝ) ^ P.certificate.stages * (P.certificate.risk.den : ℝ) :=
    mul_pos (pow_pos (by norm_num) _) hδ
  have hR : 1 / ((2 : ℝ) ^ P.certificate.stages * (P.certificate.risk.den : ℝ)) ≤
      ((P.zeroChargeRisk fee - P.certificate.risk : ℚ) : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr hlower'
    push_cast at hcast ⊢
    exact hcast
  have hgapR : 0 < ((P.zeroChargeRisk fee - P.certificate.risk : ℚ) : ℝ) := by
    exact_mod_cast sub_pos.mpr hgap
  have hinv : (((P.zeroChargeRisk fee - P.certificate.risk : ℚ) : ℝ))⁻¹ ≤
      (2 : ℝ) ^ P.certificate.stages * (P.certificate.risk.den : ℝ) := by
    simpa only [one_div, inv_inv] using inv_anti₀ (one_div_pos.mpr hD) hR
  have hlog := Real.log_le_log (inv_pos.mpr hgapR) hinv
  rw [Real.log_mul (by positivity) hδ.ne', Real.log_pow] at hlog
  exact hlog

end PDROC.DataBits
