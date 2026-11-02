module

public import PaperProofs.Paid.PDLower_FeeScale_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Statistics.BinarySymmetric

namespace PDLower

theorem fee_scalar_original {a N δ r f : ℝ} (ha : 0 < a) (hN : 1 ≤ N)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 64) (hr : 0 ≤ r) (hf : 0 ≤ f) :
    (a * N / 128) * Real.log (1 + min (f / a) (N / δ)) ≤
      a * (N * (1 - δ)) * phiReal (min (1 / 2) ((r + δ) / (N * (1 - δ)))) + f * r := by
  let β := 1 - δ
  let m := N * β
  let u := f / a
  let q := r / m
  let d := δ / m
  let W := min u (N / δ)
  let w := min u (m / δ)
  have hβ : 1 / 2 ≤ β := by dsimp [β]; linarith
  have hβ0 : 0 ≤ β := by linarith
  have hβ1 : β ≤ 1 := by dsimp [β]; linarith
  have hN0 : 0 < N := by linarith
  have hm : 0 < m := mul_pos hN0 (by linarith)
  have hmN : N / 2 ≤ m := by
    have h := mul_le_mul_of_nonneg_left hβ hN0.le
    dsimp [m]
    linarith
  have hu : 0 ≤ u := div_nonneg hf ha.le
  have hq : 0 ≤ q := div_nonneg hr hm.le
  have hd : 0 < d := div_pos hδ hm
  have hdsmall : d ≤ 1 / 63 := by
    apply (div_le_iff₀ hm).mpr
    have hbase : 63 * δ ≤ β := by dsimp [β]; linarith
    have hNβ : β ≤ m := by
      calc
        β = 1 * β := by ring
        _ ≤ N * β := mul_le_mul_of_nonneg_right hN hβ0
    linarith
  have hp : 0 < min (1 / 2) (q + d) := lt_min (by norm_num) (add_pos_of_nonneg_of_pos hq hd)
  have hscalar := fee_scalar hu hq hd hdsmall hp (min_le_left _ _) (min_le_right _ _)
  have hwd : (1 / d : ℝ) = m / δ := by dsimp [d]; field_simp
  rw [hwd] at hscalar
  change Real.log (1 + w) / 16 ≤ phiReal (min (1 / 2) (q + d)) + u * q at hscalar
  have hW0 : 0 ≤ W := le_min hu (div_nonneg hN0.le hδ.le)
  have hw0 : 0 ≤ w := le_min hu (div_nonneg hm.le hδ.le)
  have hβW : β * W ≤ w := by
    apply le_min
    · exact (mul_le_mul_of_nonneg_left (min_le_left u (N / δ)) hβ0).trans
        (mul_le_of_le_one_left hu hβ1)
    · calc
        β * W ≤ β * (N / δ) := mul_le_mul_of_nonneg_left (min_le_right _ _) hβ0
        _ = m / δ := by dsimp [m]; ring
  have hlogW : 0 ≤ Real.log (1 + W) := Real.log_nonneg (by linarith)
  have hβW0 : 0 ≤ β * W := mul_nonneg hβ0 hW0
  have hlog : β * Real.log (1 + W) ≤ Real.log (1 + w) :=
    (log_one_add_scale hβ0 hβ1 hW0).trans
      (Real.log_le_log (by nlinarith) (by linarith))
  have hcoefficient : a * N / 128 ≤ (a * m / 16) * β := by
    have hmb : N / 4 ≤ m * β := by
      calc
        _ = (N / 2) * (1 / 2) := by ring
        _ ≤ _ := mul_le_mul hmN hβ (by norm_num) hm.le
    have hmul := mul_le_mul_of_nonneg_left hmb (show 0 ≤ a / 16 by positivity)
    nlinarith
  calc
    _ = (a * N / 128) * Real.log (1 + W) := rfl
    _ ≤ ((a * m / 16) * β) * Real.log (1 + W) := mul_le_mul_of_nonneg_right hcoefficient hlogW
    _ = (a * m / 16) * (β * Real.log (1 + W)) := by ring
    _ ≤ (a * m / 16) * Real.log (1 + w) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ a * m * (phiReal (min (1 / 2) (q + d)) + u * q) := by
      have hmul := mul_le_mul_of_nonneg_left hscalar (mul_nonneg ha.le hm.le)
      nlinarith
    _ = _ := by
      have hpq : q + d = (r + δ) / m := by dsimp [q, d]; ring
      rw [hpq]
      change a * m * (phiReal (min (1 / 2) ((r + δ) / m)) + (f / a) * (r / m)) =
        a * m * phiReal (min (1 / 2) ((r + δ) / m)) + f * r
      field_simp [ha.ne', hm.ne']

end PDLower
