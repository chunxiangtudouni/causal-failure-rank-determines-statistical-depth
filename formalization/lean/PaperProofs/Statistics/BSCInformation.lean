module

public import PaperProofs.Statistics.BinarySymmetric
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Convex.Deriv

/-! The neutral scalar quantity in star-proofs.tex:40--56 and
paid-proofs.tex:38--43. Its zero-error endpoint is genuinely infinite. -/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PaperProofs.Statistics.BinarySymmetric

/-- Real formula, used only on a stated positive-error domain. -/
noncomputable def phiReal (p : ℝ) : ℝ := (1 - 2 * p) * Real.log ((1 - p) / p)

/-- The extension at zero is not obtained from Real.log 0. -/
noncomputable def phi (p : ℝ) : ℝ≥0∞ := if p = 0 then ⊤ else ENNReal.ofReal (phiReal p)

@[simp] theorem phi_zero : phi 0 = ⊤ := by simp [phi]

theorem phi_of_pos {p : ℝ} (hp : 0 < p) : phi p = ENNReal.ofReal (phiReal p) := by
  simp only [phi, ne_of_gt hp, ↓reduceIte]

@[simp] theorem phiReal_half : phiReal (1 / 2) = 0 := by norm_num [phiReal]

@[simp] theorem phi_half : phi (1 / 2) = 0 := by norm_num [phi]

theorem phiReal_nonneg {p : ℝ} (hp : 0 < p) (hhalf : p ≤ 1 / 2) : 0 ≤ phiReal p := by
  have hr : 1 ≤ (1 - p) / p := (le_div_iff₀ hp).mpr (by linarith)
  exact mul_nonneg (by linarith) (Real.log_nonneg hr)

theorem phi_ne_top {p : ℝ} (hp : 0 < p) : phi p ≠ ⊤ := by
  rw [phi_of_pos hp]
  exact ENNReal.ofReal_ne_top

noncomputable def phiDerivative (p : ℝ) : ℝ :=
  -2 * Real.log ((1 - p) / p) - (1 - 2 * p) / (p * (1 - p))

theorem hasDerivAt_log_error_odds {p : ℝ} (hp : 0 < p) (hpone : p < 1) :
    HasDerivAt (fun z : ℝ => Real.log ((1 - z) / z)) (-1 / (p * (1 - p))) p := by
  have hpn : p ≠ 0 := ne_of_gt hp
  have hon : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hpone)
  have hd := (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).div (hasDerivAt_id p) hpn).log
    (div_ne_zero hon hpn)
  convert hd using 1
  · rfl
  · dsimp
    field_simp
    ring

theorem hasDerivAt_phiReal {p : ℝ} (hp : 0 < p) (hpone : p < 1) :
    HasDerivAt phiReal (phiDerivative p) p := by
  have hd := ((hasDerivAt_const p 1).sub ((hasDerivAt_id p).const_mul 2)).mul
    (hasDerivAt_log_error_odds hp hpone)
  convert hd using 1
  · rfl
  · unfold phiDerivative
    dsimp
    ring

theorem hasDerivAt_phiDerivative {p : ℝ} (hp : 0 < p) (hpone : p < 1) :
    HasDerivAt phiDerivative (1 / (p ^ 2 * (1 - p) ^ 2)) p := by
  have hpn : p ≠ 0 := ne_of_gt hp
  have hon : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hpone)
  have hnum := (hasDerivAt_const p 1).sub ((hasDerivAt_id p).const_mul 2)
  have hden := (hasDerivAt_id p).mul ((hasDerivAt_const p 1).sub (hasDerivAt_id p))
  have hd := ((hasDerivAt_log_error_odds hp hpone).const_mul (-2)).sub
    (hnum.div hden (mul_ne_zero hpn hon))
  convert hd using 1
  · rfl
  · dsimp
    field_simp
    ring

theorem deriv_phiReal {p : ℝ} (hp : 0 < p) (hpone : p < 1) :
    deriv phiReal p = phiDerivative p := (hasDerivAt_phiReal hp hpone).deriv

theorem deriv2_phiReal {p : ℝ} (hp : 0 < p) (hpone : p < 1) :
    deriv (deriv phiReal) p = 1 / (p ^ 2 * (1 - p) ^ 2) := by
  have heq : deriv phiReal =ᶠ[nhds p] phiDerivative :=
    Filter.Eventually.mono (isOpen_Ioo.mem_nhds ⟨hp, hpone⟩) fun z hz => deriv_phiReal hz.1 hz.2
  exact ((hasDerivAt_phiDerivative hp hpone).congr_of_eventuallyEq heq).deriv

theorem phiReal_continuousOn : ContinuousOn phiReal (Set.Ioc 0 (1 / 2)) := by
  intro p hp
  exact (hasDerivAt_phiReal hp.1 (by linarith [hp.2])).continuousAt.continuousWithinAt

theorem phiReal_strictAntiOn : StrictAntiOn phiReal (Set.Ioc 0 (1 / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc _ _) phiReal_continuousOn
  intro p hp
  rw [interior_Ioc] at hp
  rw [deriv_phiReal hp.1 (by linarith [hp.2])]
  have hl : 0 < Real.log ((1 - p) / p) :=
    Real.log_pos ((lt_div_iff₀ hp.1).mpr (by linarith [hp.2]))
  have hf : 0 < (1 - 2 * p) / (p * (1 - p)) := by
    exact div_pos (by linarith [hp.2]) (mul_pos hp.1 (by linarith [hp.2]))
  unfold phiDerivative
  linarith

theorem phiReal_convexOn : ConvexOn ℝ (Set.Ioc 0 (1 / 2)) phiReal := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc _ _) phiReal_continuousOn
    (f' := phiDerivative) (f'' := fun p => 1 / (p ^ 2 * (1 - p) ^ 2)) ?_ ?_ ?_
  · intro p hp
    rw [interior_Ioc] at hp
    exact (hasDerivAt_phiReal hp.1 (by linarith [hp.2])).hasDerivWithinAt
  · intro p hp
    rw [interior_Ioc] at hp
    exact (hasDerivAt_phiDerivative hp.1 (by linarith [hp.2])).hasDerivWithinAt
  · intro p _
    exact div_nonneg zero_le_one (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem phiReal_strictConvexOn : StrictConvexOn ℝ (Set.Ioc 0 (1 / 2)) phiReal := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioc _ _) phiReal_continuousOn
  intro p hp
  rw [interior_Ioc] at hp
  change 0 < deriv (deriv phiReal) p
  rw [deriv2_phiReal hp.1 (by linarith [hp.2])]
  exact div_pos zero_lt_one (mul_pos (sq_pos_of_pos hp.1) (sq_pos_of_pos (by linarith [hp.2])))

/-- Exact scalar obligations, separated from the experiment and its input.
No monotonicity or convexity assertion is an assumed test field. -/
def PhiScalarClaims : Prop :=
  StrictAntiOn phiReal (Set.Ioc 0 (1 / 2)) ∧
  ConvexOn ℝ (Set.Ioc 0 (1 / 2)) phiReal ∧
  ∀ p ∈ Set.Ioc (0 : ℝ) (1 / 2), deriv (deriv phiReal) p = 1 / (p ^ 2 * (1 - p) ^ 2)

theorem phiScalarClaims : PhiScalarClaims :=
  ⟨phiReal_strictAntiOn, phiReal_convexOn, fun _ hp => deriv2_phiReal hp.1 (by linarith [hp.2])⟩

end PaperProofs.Statistics.BinarySymmetric
