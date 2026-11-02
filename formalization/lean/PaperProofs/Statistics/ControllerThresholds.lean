module

public import PaperProofs.Statistics.IteratedLog
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.Linarith

/-!
The exact integer/rational thresholds in the frozen price-proofs.tex:169--184.
The index zero is unused; paper indices start at one. All controller values
are computed by rational ceilings and natural-number integer logarithms.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace PaperProofs.Statistics

def thresholdSequence (initial : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => initial
  | j + 2 => Nat.clog 2 (2 + thresholdSequence initial (j + 1))

def controllerB (risk : ℚ) (j : ℕ) : ℕ :=
  thresholdSequence (Nat.clog 2 ⌈1 / risk⌉₊) j

def controllerTarget (risk : ℚ) (j : ℕ) : ℚ :=
  1 / (4 * (1 + controllerB risk j))

@[simp] theorem controllerB_one (risk : ℚ) : controllerB risk 1 = Nat.clog 2 ⌈1 / risk⌉₊ := rfl

theorem controllerB_succ (risk : ℚ) (j : ℕ) (hj : 1 ≤ j) :
    controllerB risk (j + 1) = Nat.clog 2 (2 + controllerB risk j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
  rfl

theorem two_add_le_two_pow (n : ℕ) (hn : 2 ≤ n) : 2 + n ≤ 2 ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show 2 + (k + 1) = (2 + k) + 1 by omega, Nat.pow_succ]
    nlinarith

theorem clog_two_add_le (n : ℕ) (hn : 2 ≤ n) : Nat.clog 2 (2 + n) ≤ n :=
  (Nat.clog_le_iff_le_pow (by norm_num)).mpr (two_add_le_two_pow n hn)

theorem clog_two_add_ge_two (n : ℕ) (hn : 2 ≤ n) : 2 ≤ Nat.clog 2 (2 + n) := by
  have h : 1 < Nat.clog 2 (2 + n) :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by simpa using (show 2 < 2 + n by omega))
  omega

theorem thresholdSequence_bounds (initial : ℕ) (hinit : 2 ≤ initial) (j : ℕ) (hj : 1 ≤ j) :
    2 ≤ thresholdSequence initial j ∧ thresholdSequence initial j ≤ initial := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
  clear hj
  induction k with
  | zero => exact ⟨hinit, le_rfl⟩
  | succ k ih =>
    change 2 ≤ Nat.clog 2 (2 + thresholdSequence initial (k + 1)) ∧
      Nat.clog 2 (2 + thresholdSequence initial (k + 1)) ≤ initial
    exact ⟨clog_two_add_ge_two _ ih.1, (clog_two_add_le _ ih.1).trans ih.2⟩

theorem controllerB_initial_ge_two (risk : ℚ) (hrisk : 0 < risk) (hquarter : risk ≤ 1 / 4) :
    2 ≤ controllerB risk 1 := by
  have hinv : (4 : ℚ) ≤ 1 / risk := (le_div_iff₀ hrisk).mpr (by linarith)
  have hceil : 4 ≤ ⌈1 / risk⌉₊ := by
    have h := hinv.trans (Nat.le_ceil (1 / risk))
    exact_mod_cast h
  have h : 1 < Nat.clog 2 ⌈1 / risk⌉₊ :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by simpa using (show 2 < ⌈1 / risk⌉₊ by omega))
  exact h

theorem controllerB_initial_le_inverse (risk : ℚ) (hrisk : 0 < risk) (hquarter : risk ≤ 1 / 4) :
    (controllerB risk 1 : ℚ) ≤ 1 / risk := by
  have hceil : 1 ≤ ⌈1 / risk⌉₊ := by
    have hge := controllerB_initial_ge_two risk hrisk hquarter
    by_contra h
    have hz : ⌈1 / risk⌉₊ = 0 := by omega
    simp only [controllerB_one, hz, Nat.clog_zero_right] at hge
    omega
  have hpow : ⌈1 / risk⌉₊ ≤ 2 ^ (⌈1 / risk⌉₊ - 1) := by
    have h := Nat.lt_pow_self (n := ⌈1 / risk⌉₊ - 1) (show 1 < 2 by norm_num)
    omega
  have hclog := (Nat.clog_le_iff_le_pow (by norm_num)).mpr hpow
  have hclogQ : (controllerB risk 1 : ℚ) ≤ (⌈1 / risk⌉₊ : ℚ) - 1 := by
    simpa only [controllerB_one, Nat.cast_sub hceil, Nat.cast_one] using
      (show (Nat.clog 2 ⌈1 / risk⌉₊ : ℚ) ≤ (⌈1 / risk⌉₊ - 1 : ℕ) by exact_mod_cast hclog)
  have hceil_lt := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ 1 / risk from (one_div_pos.mpr hrisk).le)
  linarith

theorem controllerB_bounds (risk : ℚ) (hrisk : 0 < risk) (hquarter : risk ≤ 1 / 4)
    (j : ℕ) (hj : 1 ≤ j) :
    2 ≤ controllerB risk j ∧ controllerB risk j ≤ controllerB risk 1 ∧
      (controllerB risk j : ℚ) ≤ 1 / risk := by
  have h := thresholdSequence_bounds (controllerB risk 1) (controllerB_initial_ge_two risk hrisk hquarter) j hj
  refine ⟨h.1, h.2, ?_⟩
  exact (by exact_mod_cast h.2 : (controllerB risk j : ℚ) ≤ (controllerB risk 1 : ℚ)).trans
    (controllerB_initial_le_inverse risk hrisk hquarter)

theorem controllerTarget_pos (risk : ℚ) (j : ℕ) : 0 < controllerTarget risk j := by
  unfold controllerTarget
  positivity

theorem controllerTarget_le_quarter (risk : ℚ) (j : ℕ) : controllerTarget risk j ≤ 1 / 4 := by
  unfold controllerTarget
  apply one_div_le_one_div_of_le (by norm_num)
  have h : (0 : ℚ) ≤ controllerB risk j := Nat.cast_nonneg _
  linarith

theorem controllerTarget_floor (risk : ℚ) (hrisk : 0 < risk) (hquarter : risk ≤ 1 / 4)
    (j : ℕ) (hj : 1 ≤ j) : risk / 6 ≤ controllerTarget risk j := by
  have hB := (controllerB_bounds risk hrisk hquarter j hj).2.2
  have hmul : risk * (controllerB risk j : ℚ) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hB hrisk.le
    simpa only [mul_one_div_cancel (ne_of_gt hrisk)] using h
  unfold controllerTarget
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < 4 * (1 + controllerB risk j))).mpr
  nlinarith

/-- Equality with the genuine real ceil(log₂ q), derived from its dyadic
integer-comparison characterization. The real log is only an analysis map. -/
theorem clog_ceil_rat_eq_natCeil_logb (q : ℚ) (hq : 0 < q) :
    Nat.clog 2 ⌈q⌉₊ = ⌈Real.logb 2 (q : ℝ)⌉₊ := by
  apply eq_of_forall_ge_iff
  intro n
  rw [Nat.clog_le_iff_le_pow (by norm_num), Nat.ceil_le, Nat.ceil_le,
    Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hq), Real.rpow_natCast]
  constructor <;> intro h <;> exact_mod_cast h

noncomputable def analyticControllerB (z : ℝ) (j : ℕ) : ℕ :=
  thresholdSequence ⌈Real.logb 2 z⌉₊ j

@[simp] theorem analyticControllerB_one (z : ℝ) : analyticControllerB z 1 = ⌈Real.logb 2 z⌉₊ := rfl

theorem analyticControllerB_succ (z : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    analyticControllerB z (j + 1) = ⌈Real.logb 2 (2 + (analyticControllerB z j : ℝ))⌉₊ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
  change Nat.clog 2 (2 + thresholdSequence ⌈Real.logb 2 z⌉₊ (k + 1)) = _
  simpa only [analyticControllerB, Nat.cast_add, Nat.cast_ofNat] using
    (Real.natCeil_logb_natCast 2 (2 + thresholdSequence ⌈Real.logb 2 z⌉₊ (k + 1))).symm

theorem controllerB_eq_analytic (risk : ℚ) (hrisk : 0 < risk) (j : ℕ) :
    controllerB risk j = analyticControllerB (1 / (risk : ℝ)) j := by
  unfold controllerB analyticControllerB
  congr 1
  simpa only [Rat.cast_div, Rat.cast_one] using clog_ceil_rat_eq_natCeil_logb (1 / risk) (one_div_pos.mpr hrisk)

theorem controllerB_one_eq_intCeil (risk : ℚ) (hrisk : 0 < risk) (hquarter : risk ≤ 1 / 4) :
    (controllerB risk 1 : ℤ) = ⌈Real.logb 2 (1 / (risk : ℝ))⌉ := by
  rw [controllerB_eq_analytic risk hrisk 1, analyticControllerB_one]
  apply Int.natCast_ceil_eq_ceil
  apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
  have hrR : (0 : ℝ) < risk := by exact_mod_cast hrisk
  have hqR : (risk : ℝ) ≤ 1 / 4 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hquarter
    norm_num at h
    exact h
  exact (le_div_iff₀ hrR).mpr (by linarith)

theorem controllerB_succ_eq_intCeil (risk : ℚ) (j : ℕ) (hj : 1 ≤ j) :
    (controllerB risk (j + 1) : ℤ) = ⌈Real.logb 2 (2 + (controllerB risk j : ℝ))⌉ := by
  rw [controllerB_succ risk j hj, ← Real.natCeil_logb_natCast]
  have hlog : 0 ≤ Real.logb 2 ((2 + controllerB risk j : ℕ) : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ 2 + controllerB risk j by omega))
  simpa only [Nat.cast_add, Nat.cast_ofNat] using Int.natCast_ceil_eq_ceil hlog

theorem log_difference_tendsto_of_ratio {α : Type*} {l : Filter α} {f g : α → ℝ} {c : ℝ}
    (hc : 0 < c) (hratio : Tendsto (fun z => f z / g z) l (𝓝 c)) (hg : Tendsto g l atTop) :
    Tendsto (fun z => Real.log (f z) - Real.log (g z)) l (𝓝 (Real.log c)) := by
  have hlog := hratio.log (ne_of_gt hc)
  apply hlog.congr'
  have hgp : ∀ᶠ z in l, 0 < g z := hg.eventually_gt_atTop 0
  have hrp : ∀ᶠ z in l, 0 < f z / g z := hratio.eventually (lt_mem_nhds hc)
  filter_upwards [hgp, hrp] with z hgz hrz
  have hfp : 0 < f z := by
    have h := mul_pos hrz hgz
    simpa only [div_mul_cancel₀ _ (ne_of_gt hgz)] using h
  exact Real.log_div (ne_of_gt hfp) (ne_of_gt hgz)

theorem log_ratio_tendsto_one_of_ratio {α : Type*} {l : Filter α} {f g : α → ℝ} {c : ℝ}
    (hc : 0 < c) (hratio : Tendsto (fun z => f z / g z) l (𝓝 c)) (hg : Tendsto g l atTop) :
    Tendsto (fun z => Real.log (f z) / Real.log (g z)) l (𝓝 1) := by
  have hlogg := Real.tendsto_log_atTop.comp hg
  have hzero := (log_difference_tendsto_of_ratio hc hratio hg).div_atTop hlogg
  have hconst : Tendsto (fun _z : α => (1 : ℝ)) l (𝓝 1) := tendsto_const_nhds
  have hone := hconst.add hzero
  apply (show Tendsto (fun z => (1 : ℝ) + (Real.log (f z) - Real.log (g z)) / Real.log (g z)) l (𝓝 1)
    from by simpa only [Function.comp_def, add_zero] using hone).congr'
  filter_upwards [hlogg.eventually_ne_atTop 0] with z hz
  change Real.log (g z) ≠ 0 at hz
  field_simp [hz]
  ring

theorem tendsto_atTop_of_ratio_pos {α : Type*} {l : Filter α} {f g : α → ℝ} {c : ℝ}
    (hc : 0 < c) (hratio : Tendsto (fun z => f z / g z) l (𝓝 c)) (hg : Tendsto g l atTop) :
    Tendsto f l atTop := by
  have h := Filter.Tendsto.pos_mul_atTop hc hratio hg
  apply h.congr'
  filter_upwards [hg.eventually_ne_atTop 0] with z hz
  exact div_mul_cancel₀ _ hz

theorem natCeil_logb_div_log_tendsto {α : Type*} {l : Filter α} {f : α → ℝ}
    (hf : Tendsto f l atTop) :
    Tendsto (fun z => (⌈Real.logb 2 (f z)⌉₊ : ℝ) / Real.log (f z)) l (𝓝 (1 / Real.log 2)) := by
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.tendsto_log_atTop.comp hf
  have hv : Tendsto (fun z => Real.logb 2 (f z)) l atTop :=
    Filter.Tendsto.atTop_div_const hd hlog
  have hceil : Tendsto (fun z => (⌈Real.logb 2 (f z)⌉₊ : ℝ) / Real.logb 2 (f z)) l (𝓝 1) :=
    tendsto_nat_ceil_div_atTop.comp hv
  apply (hceil.div_const (Real.log 2)).congr'
  filter_upwards [hlog.eventually_ne_atTop 0] with z hz
  change Real.log (f z) ≠ 0 at hz
  simp only [Real.logb]
  field_simp [hz, ne_of_gt hd]

theorem analyticControllerB_ratio (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun z : ℝ => (analyticControllerB z j : ℝ) / iteratedLog j z)
      atTop (𝓝 (1 / Real.log 2)) := by
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < 1 / Real.log 2 := one_div_pos.mpr hd
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
  clear hj
  induction n with
  | zero => exact natCeil_logb_div_log_tendsto tendsto_id
  | succ n ih =>
    have hell := iteratedLog_tendsto_atTop (n + 1)
    have htwoRatio : Tendsto
        (fun z : ℝ => (2 + (analyticControllerB z (n + 1) : ℝ)) / iteratedLog (n + 1) z)
        atTop (𝓝 (1 / Real.log 2)) := by
      have hz : Tendsto (fun z : ℝ => (2 : ℝ) / iteratedLog (n + 1) z) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hell
      simpa only [add_div, zero_add] using hz.add ih
    have htwo := tendsto_atTop_of_ratio_pos hc htwoRatio hell
    have hlogRatio := log_ratio_tendsto_one_of_ratio hc htwoRatio hell
    have hceil := natCeil_logb_div_log_tendsto htwo
    have hprod := hceil.mul hlogRatio
    have hprod' : Tendsto (fun z : ℝ =>
        ((⌈Real.logb 2 (2 + (analyticControllerB z (n + 1) : ℝ))⌉₊ : ℝ) /
          Real.log (2 + (analyticControllerB z (n + 1) : ℝ))) *
        (Real.log (2 + (analyticControllerB z (n + 1) : ℝ)) / iteratedLog (n + 2) z))
        atTop (𝓝 (1 / Real.log 2)) := by
      simpa only [iteratedLog, mul_one] using hprod
    apply hprod'.congr'
    filter_upwards [(Real.tendsto_log_atTop.comp htwo).eventually_ne_atTop 0,
      (iteratedLog_tendsto_atTop (n + 2)).eventually_ne_atTop 0] with z hlog hellz
    change Real.log (2 + (analyticControllerB z (n + 1) : ℝ)) ≠ 0 at hlog
    rw [analyticControllerB_succ z (n + 1) (by omega)]
    field_simp [hlog, hellz]

theorem analyticControllerB_tendsto_atTop (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun z : ℝ => (analyticControllerB z j : ℝ)) atTop atTop :=
  tendsto_atTop_of_ratio_pos (one_div_pos.mpr (Real.log_pos (by norm_num)))
    (analyticControllerB_ratio j hj) (iteratedLog_tendsto_atTop j)

theorem analyticControllerB_add_one_ratio (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun z : ℝ => (1 + (analyticControllerB z j : ℝ)) / iteratedLog j z)
      atTop (𝓝 (1 / Real.log 2)) := by
  have hz : Tendsto (fun z : ℝ => (1 : ℝ) / iteratedLog j z) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (iteratedLog_tendsto_atTop j)
  simpa only [add_div, zero_add] using hz.add (analyticControllerB_ratio j hj)

/-- A stronger form of the frozen O_j(1): for every fixed positive j the
additive difference has the same explicit finite limit. -/
theorem analyticControllerTarget_log_difference (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun z : ℝ => Real.log (4 * (1 + (analyticControllerB z j : ℝ))) -
        iteratedLog (j + 1) z) atTop (𝓝 (Real.log 4 + Real.log (1 / Real.log 2))) := by
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiff := log_difference_tendsto_of_ratio (one_div_pos.mpr hd)
    (analyticControllerB_add_one_ratio j hj) (iteratedLog_tendsto_atTop j)
  have hconst : Tendsto (fun _z : ℝ => Real.log 4) atTop (𝓝 (Real.log 4)) := tendsto_const_nhds
  apply (hconst.add hdiff).congr'
  exact Filter.Eventually.of_forall (fun z => by
    change Real.log 4 + (Real.log (1 + (analyticControllerB z j : ℝ)) - Real.log (iteratedLog j z)) =
      Real.log (4 * (1 + (analyticControllerB z j : ℝ))) - iteratedLog (j + 1) z
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (ne_of_gt (by positivity : (0 : ℝ) < 1 + (analyticControllerB z j : ℝ)))]
    simp only [iteratedLog]
    ring)

theorem analyticControllerTarget_mul_iteratedLog (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun z : ℝ => (1 / (4 * (1 + (analyticControllerB z j : ℝ)))) * iteratedLog j z)
      atTop (𝓝 (Real.log 2 / 4)) := by
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (1 / Real.log 2) ≠ 0 := ne_of_gt (one_div_pos.mpr hd)
  have h := (analyticControllerB_add_one_ratio j hj).inv₀ hc
  have h' : Tendsto (fun z : ℝ => ((1 + (analyticControllerB z j : ℝ)) / iteratedLog j z)⁻¹ / 4)
      atTop (𝓝 (Real.log 2 / 4)) := by simpa only [one_div, inv_inv] using h.div_const 4
  apply h'.congr'
  filter_upwards [(iteratedLog_tendsto_atTop j).eventually_ne_atTop 0] with z hz
  field_simp [hz]

theorem rationalInverse_tendsto_atTop :
    Tendsto (fun risk : ℚ => 1 / (risk : ℝ)) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hcast : Tendsto (fun risk : ℚ => (risk : ℝ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Rat.cast_zero] using (Rat.continuous_coe_real.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with risk hrisk
      change (0 : ℝ) < (risk : ℝ)
      have hr : (0 : ℚ) < risk := hrisk
      exact_mod_cast hr
  simpa only [Function.comp_def, one_div] using (tendsto_inv_nhdsGT_zero :
    Tendsto (fun z : ℝ => z⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop).comp hcast

theorem controllerTarget_inverse_real (risk : ℚ) (j : ℕ) :
    1 / (controllerTarget risk j : ℝ) = 4 * (1 + (controllerB risk j : ℝ)) := by
  simp only [controllerTarget, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_add, Rat.cast_natCast, one_div_one_div]

theorem controllerTarget_real (risk : ℚ) (j : ℕ) :
    (controllerTarget risk j : ℝ) = 1 / (4 * (1 + (controllerB risk j : ℝ))) := by
  simp only [controllerTarget, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_add, Rat.cast_natCast]

theorem controllerTarget_log_difference_tendsto (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun risk : ℚ => Real.log (1 / (controllerTarget risk j : ℝ)) -
        iteratedLog (j + 1) (1 / (risk : ℝ))) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (Real.log 4 + Real.log (1 / Real.log 2))) := by
  apply ((analyticControllerTarget_log_difference j hj).comp rationalInverse_tendsto_atTop).congr'
  filter_upwards [self_mem_nhdsWithin] with risk hrisk
  rw [controllerTarget_inverse_real, controllerB_eq_analytic risk hrisk j]
  rfl

theorem controllerTarget_log_error_isBigO (j : ℕ) (hj : 1 ≤ j) :
    (fun risk : ℚ => Real.log (1 / (controllerTarget risk j : ℝ)) -
      iteratedLog (j + 1) (1 / (risk : ℝ))) =O[nhdsWithin 0 (Set.Ioi 0)] (fun _risk => (1 : ℝ)) :=
  (controllerTarget_log_difference_tendsto j hj).isBigO_one ℝ

theorem controllerTarget_mul_iteratedLog_tendsto (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun risk : ℚ => (controllerTarget risk j : ℝ) * iteratedLog j (1 / (risk : ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (Real.log 2 / 4)) := by
  apply ((analyticControllerTarget_mul_iteratedLog j hj).comp rationalInverse_tendsto_atTop).congr'
  filter_upwards [self_mem_nhdsWithin] with risk hrisk
  rw [controllerTarget_real, controllerB_eq_analytic risk hrisk j]
  rfl

theorem controllerTarget_iteratedLog_isBigO (j : ℕ) (hj : 1 ≤ j) :
    (fun risk : ℚ => (controllerTarget risk j : ℝ)) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun risk => 1 / iteratedLog j (1 / (risk : ℝ))) := by
  refine isBigO_of_div_tendsto_nhds ?_ (Real.log 2 / 4) ?_
  · filter_upwards [((iteratedLog_tendsto_atTop j).comp rationalInverse_tendsto_atTop).eventually_ne_atTop 0]
      with risk hrisk
    exact fun hzero => ((one_div_ne_zero hrisk) hzero).elim
  · apply (controllerTarget_mul_iteratedLog_tendsto j hj).congr'
    exact Filter.Eventually.of_forall (fun risk => by
      change (controllerTarget risk j : ℝ) * iteratedLog j (1 / (risk : ℝ)) =
        (controllerTarget risk j : ℝ) / (1 / iteratedLog j (1 / (risk : ℝ)))
      simp only [div_eq_mul_inv, one_mul, inv_inv])

/-- The quota target floor keeps the original real delta. Only the controller's
current risk and threshold target are rational. -/
theorem controllerTarget_native_floor (delta : ℝ) (N : ℕ) (risk : ℚ)
    (hrisk : 0 < risk) (hquarter : risk ≤ 1 / 4)
    (hpath : delta / (2 : ℝ) ^ (N + 1) ≤ (risk : ℝ)) (j : ℕ) (hj : 1 ≤ j) :
    delta / (6 * (2 : ℝ) ^ (N + 1)) ≤ (controllerTarget risk j : ℝ) := by
  have htarget : (risk : ℝ) / 6 ≤ (controllerTarget risk j : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr (controllerTarget_floor risk hrisk hquarter j hj)
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  calc
    _ = (delta / (2 : ℝ) ^ (N + 1)) / 6 := by ring
    _ ≤ (risk : ℝ) / 6 := div_le_div_of_nonneg_right hpath (by norm_num)
    _ ≤ _ := htarget

theorem noToolTarget_native_floor (delta : ℝ) (N : ℕ) (risk : ℚ) (hrisk : 0 < risk)
    (hpath : delta / (2 : ℝ) ^ (N + 1) ≤ (risk : ℝ)) :
    delta / (6 * (2 : ℝ) ^ (N + 1)) ≤ ((risk / 2 : ℚ) : ℝ) := by
  have hr : (0 : ℝ) < risk := by exact_mod_cast hrisk
  push_cast
  calc
    _ = (delta / (2 : ℝ) ^ (N + 1)) / 6 := by ring
    _ ≤ (risk : ℝ) / 6 := div_le_div_of_nonneg_right hpath (by norm_num)
    _ ≤ (risk : ℝ) / 2 := by linarith

/-- The exact bad-child risk allocation of price-proofs.tex:195--197. -/
def controllerBadRisk (risk target : ℚ) : ℚ := min (1 / 4) (risk / (2 * target))

theorem controllerBadRisk_bounds (risk target : ℚ) (hrisk : 0 < risk)
    (hquarter : risk ≤ 1 / 4) (htarget : 0 < target) (htargetQuarter : target ≤ 1 / 4) :
    risk ≤ controllerBadRisk risk target ∧ controllerBadRisk risk target ≤ 1 / 4 := by
  refine ⟨le_min hquarter ?_, min_le_left _ _⟩
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2 * target)).mpr
  nlinarith

theorem controllerBadRisk_positive (risk target : ℚ) (hrisk : 0 < risk)
    (hquarter : risk ≤ 1 / 4) (htarget : 0 < target) (htargetQuarter : target ≤ 1 / 4) :
    0 < controllerBadRisk risk target :=
  hrisk.trans_le (controllerBadRisk_bounds risk target hrisk hquarter htarget htargetQuarter).1

theorem controllerBadRisk_budget (risk target : ℚ) (htarget : 0 < target) :
    target * controllerBadRisk risk target ≤ risk / 2 := by
  have h := mul_le_mul_of_nonneg_left (min_le_right (1 / 4) (risk / (2 * target))) htarget.le
  calc
    _ ≤ target * (risk / (2 * target)) := h
    _ = _ := by field_simp [ne_of_gt htarget]

/-- Together with the exact correct-child allocation r/2, this is the
numerical step needed for the pathwise floor, not an assumed policy invariant. -/
theorem controllerBadRisk_ge_half (risk target : ℚ) (hrisk : 0 < risk)
    (hquarter : risk ≤ 1 / 4) (htarget : 0 < target) (htargetQuarter : target ≤ 1 / 4) :
    risk / 2 ≤ controllerBadRisk risk target := by
  exact (by linarith : risk / 2 ≤ risk).trans
    (controllerBadRisk_bounds risk target hrisk hquarter htarget htargetQuarter).1

end PaperProofs.Statistics
