module

public import PaperProofs.Paid.Claims
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDLower

noncomputable def symmetricLogOdds (g : ℝ) : ℝ := Real.log (1 + 2 * g) - Real.log (1 - 2 * g)

theorem hasDerivAt_symmetricLogOdds {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4) :
    HasDerivAt symmetricLogOdds (4 / (1 - 4 * g ^ 2)) g := by
  have hp : 0 < 1 + 2 * g := by linarith
  have hm : 0 < 1 - 2 * g := by linarith
  have hsq : g ^ 2 ≤ 1 / 16 := by nlinarith [mul_self_le_mul_self hg0 hg1]
  have hden : 1 - g ^ 2 * 4 ≠ 0 := ne_of_gt (by linarith)
  have hp' : 1 + g * 2 ≠ 0 := by linarith
  have hm' : 1 - g * 2 ≠ 0 := by linarith
  have hd := (((hasDerivAt_const g 1).add ((hasDerivAt_id g).const_mul 2)).log hp.ne').sub
    (((hasDerivAt_const g 1).sub ((hasDerivAt_id g).const_mul 2)).log hm.ne')
  convert hd using 1
  · funext x
    rfl
  · simp only [Pi.add_apply, Pi.sub_apply, id_eq, mul_one, zero_add, zero_sub]
    ring_nf
    field_simp [hp', hm', hden]
    ring
theorem symmetricLogOdds_upper {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4) :
    symmetricLogOdds g ≤ (16 / 3) * g := by
  let F : ℝ → ℝ := fun x => (16 / 3) * x - symmetricLogOdds x
  have hd (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (1 / 4)) :
      HasDerivAt F ((16 / 3) - 4 / (1 - 4 * x ^ 2)) x := by
    convert ((hasDerivAt_id x).const_mul (16 / 3)).sub (hasDerivAt_symmetricLogOdds hx.1 hx.2) using 1
    · funext y
      rfl
    · norm_num
  have hc : ContinuousOn F (Set.Icc (0 : ℝ) (1 / 4)) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Set.Icc (0 : ℝ) (1 / 4))) :=
    fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hsign (x : ℝ) (hx : x ∈ interior (Set.Icc (0 : ℝ) (1 / 4))) : 0 ≤ deriv F x := by
    have hxc : x ∈ Set.Icc (0 : ℝ) (1 / 4) := interior_subset hx
    have hsq : x ^ 2 ≤ 1 / 16 := by nlinarith [mul_self_le_mul_self hxc.1 hxc.2]
    have hden : 0 < 1 - 4 * x ^ 2 := by linarith
    rw [(hd x hxc).deriv]
    exact sub_nonneg.mpr ((div_le_iff₀ hden).mpr (by nlinarith))
  have hm : MonotoneOn F (Set.Icc (0 : ℝ) (1 / 4)) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc hdiff hsign
  have h := hm (show (0 : ℝ) ∈ Set.Icc 0 (1 / 4) by constructor <;> norm_num) ⟨hg0, hg1⟩ hg0
  have hz : F 0 = 0 := by norm_num [F, symmetricLogOdds]
  rw [hz] at h
  dsimp [F] at h
  linarith

theorem log_two_upper : Real.log 2 ≤ 3 / 4 := by
  have h : Real.log 2 ≤ Real.log ((9 / 8 : ℝ) ^ 6) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h
  have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 / 8 by norm_num)
  norm_num at h hl
  linarith

theorem log_two_lower : (37 / 60 : ℝ) ≤ Real.log 2 := by
  have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
  have h3 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 6 / 5 by norm_num)
  have heq : Real.log 2 = Real.log (4 / 3) + Real.log (5 / 4) + Real.log (6 / 5) := by
    calc
      _ = Real.log (((4 / 3 : ℝ) * (5 / 4)) * (6 / 5)) := by norm_num
      _ = _ := by rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  norm_num at h1 h2 h3
  linarith

theorem saturationLog_lower {N δ : ℝ} (hN : 1 ≤ N) (hd : 0 < δ) (hd64 : δ ≤ 1 / 64) :
    (37 / 10 : ℝ) ≤ Real.log (1 + N / δ) := by
  have hr : 64 ≤ N / δ := (le_div_iff₀ hd).mpr (by linarith)
  have hl : Real.log 64 ≤ Real.log (1 + N / δ) := Real.log_le_log (by norm_num) (by linarith)
  have heq : Real.log 64 = 6 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 6
    norm_num at h
    exact h
  rw [heq] at hl
  linarith [log_two_lower]

end PDLower
