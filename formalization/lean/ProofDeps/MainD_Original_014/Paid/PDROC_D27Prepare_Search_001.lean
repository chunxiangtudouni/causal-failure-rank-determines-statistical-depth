module

public import PaperProofs.Paid.Model

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid

namespace PDROC.D27Prepare.Search

/-- Number of rejected odd candidates before the original least t0.
This is a proof index for the literal loop, not a machine instruction. -/
def majorityIndex (D : CertificateInput) : ℕ := (D.t0 - 1) / 2

theorem t0_eq_two_mul_index_add_one (D : CertificateInput) :
    D.t0 = 2 * majorityIndex D + 1 := by
  obtain ⟨j, hj⟩ := D.t0_spec.2.1
  unfold majorityIndex
  omega

theorem majority_counter_le (D : CertificateInput) (j : ℕ) (hj : j ≤ majorityIndex D) :
    2 * j + 1 ≤ D.t0 := by
  rw [t0_eq_two_mul_index_add_one D]
  omega

theorem majority_guard_iff (D : CertificateInput) (j : ℕ) (hj : j ≤ majorityIndex D) :
    D.varianceBase ^ (2 * j + 1) ≤ (D.risk / (2 * (D.stages : ℚ))) ^ 2 ↔
      j = majorityIndex D := by
  constructor
  · intro guard
    have qualifies : D.MajorityQualifies (2 * j + 1) := ⟨by omega, ⟨j, by omega⟩, guard⟩
    have minimum := D.t0_min qualifies
    have exactIndex := t0_eq_two_mul_index_add_one D
    omega
  · intro equal
    subst j
    simpa only [t0_eq_two_mul_index_add_one D] using D.t0_spec.2.2

theorem majority_power_step (D : CertificateInput) (j : ℕ) :
    D.varianceBase ^ (2 * (j + 1) + 1) =
      D.varianceBase ^ (2 * j + 1) * D.varianceBase ^ 2 := by
  rw [← pow_add]
  congr 1

theorem majority_power_bounds (D : CertificateInput) (j : ℕ) :
    0 ≤ D.varianceBase ^ (2 * j + 1) ∧ D.varianceBase ^ (2 * j + 1) ≤ 1 := by
  have upper : D.varianceBase ^ (2 * j + 1) ≤ D.varianceBase ^ 0 :=
    pow_le_pow_of_le_one D.varianceBase_nonneg D.varianceBase_lt_one.le (Nat.zero_le _)
  exact ⟨pow_nonneg D.varianceBase_nonneg _, by simpa only [pow_zero] using upper⟩

/-- The machine can test this without rational division. The positive
original denominator makes it exactly the original rocError guard. -/
theorem endpoint_guard_iff (D : CertificateInput) (m : ℕ) :
    (1 : ℚ) ≤ D.menuRatio * (1 + D.odds ^ m) ↔ D.rocError m ≤ D.menuRatio := by
  change (1 : ℚ) ≤ D.menuRatio * (1 + D.odds ^ m) ↔
    1 / (1 + D.odds ^ m) ≤ D.menuRatio
  exact (div_le_iff₀ (add_pos (by norm_num : (0 : ℚ) < 1) (pow_pos D.odds_pos m))).symm

theorem endpoint_guard_eq_iff (D : CertificateInput) (m : ℕ) (hm : m ≤ D.M) :
    (1 : ℚ) ≤ D.menuRatio * (1 + D.odds ^ m) ↔ m = D.M := by
  rw [endpoint_guard_iff]
  constructor
  · intro guard
    exact Nat.le_antisymm hm (D.M_min guard)
  · intro equal
    subst m
    exact D.M_spec

theorem endpoint_power_step (D : CertificateInput) (m : ℕ) :
    D.odds ^ (m + 1) = D.odds ^ m * D.odds := pow_succ _ _

theorem endpoint_power_bounds (D : CertificateInput) (m : ℕ) (hm : m ≤ D.M) :
    1 ≤ D.odds ^ m ∧ D.odds ^ m ≤ D.odds ^ D.M := by
  have lower : D.odds ^ 0 ≤ D.odds ^ m := pow_le_pow_right₀ D.odds_gt_one.le (Nat.zero_le m)
  exact ⟨by simpa only [pow_zero] using lower, pow_le_pow_right₀ D.odds_gt_one.le hm⟩

theorem exponent_guard_iff (D : CertificateInput) (e : ℕ) (he : 1 ≤ e) (hle : e ≤ D.E) :
    (1 / 2 : ℚ) ^ e ≤ D.gamma * D.epsilon ↔ e = D.E := by
  constructor
  · intro guard
    exact Nat.le_antisymm hle (D.E_min ⟨he, guard⟩)
  · intro equal
    subst e
    exact D.E_spec.2

theorem exponent_initial_le (D : CertificateInput) : 1 ≤ D.E := D.E_spec.1

theorem exponent_power_step (e : ℕ) :
    (1 / 2 : ℚ) ^ (e + 1) = (1 / 2 : ℚ) ^ e * (1 / 2 : ℚ) := pow_succ _ _

theorem exponent_power_bounds (e : ℕ) :
    0 ≤ (1 / 2 : ℚ) ^ e ∧ (1 / 2 : ℚ) ^ e ≤ 1 := by
  have upper : (1 / 2 : ℚ) ^ e ≤ (1 / 2 : ℚ) ^ 0 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.zero_le e)
  exact ⟨pow_nonneg (by norm_num) _, by simpa only [pow_zero] using upper⟩

end PDROC.D27Prepare.Search
