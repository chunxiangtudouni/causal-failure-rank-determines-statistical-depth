module

public import Paid.PDROC_D27Prepare_Search_001
public import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid

namespace PDROC.D27Prepare.Search

/-- The quotient/remainder computation used by the literal ceiling pages.
Both arithmetic instructions have a strictly positive actual denominator. -/
def ceilingValue (q : ℚ) : ℕ :=
  q.num.natAbs / q.den + if q.num.natAbs % q.den = 0 then 0 else 1

theorem ceil_nat_ratio (a b : ℕ) (hb : 0 < b) :
    Nat.ceil ((a : ℚ) / (b : ℚ)) = a / b + if a % b = 0 then 0 else 1 := by
  have positive : (0 : ℚ) < b := by exact_mod_cast hb
  have decomposedNat : a = a / b * b + a % b := by
    simpa only [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div a b).symm
  have decomposed : (a : ℚ) = (a / b : ℕ) * (b : ℚ) + (a % b : ℕ) := by
    exact_mod_cast decomposedNat
  by_cases remainder : a % b = 0
  · simp only [remainder, ite_true, Nat.add_zero]
    have fraction : (a : ℚ) / (b : ℚ) = (a / b : ℕ) := by
      apply (div_eq_iff positive.ne').mpr
      simpa only [remainder, Nat.cast_zero, add_zero] using decomposed
    rw [fraction]
    exact Nat.ceil_natCast _
  · simp only [remainder, ite_false]
    apply (Nat.ceil_eq_iff (n := a / b + 1)
      (a := (a : ℚ) / (b : ℚ)) (Nat.succ_ne_zero (a / b))).mpr
    have remainderPos : (0 : ℚ) < (a % b : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero remainder
    have remainderLt : ((a % b : ℕ) : ℚ) < b := by exact_mod_cast Nat.mod_lt a hb
    constructor
    · simp only [Nat.add_sub_cancel]
      apply (lt_div_iff₀ positive).mpr
      linarith
    · apply (div_le_iff₀ positive).mpr
      push_cast
      nlinarith

theorem ceilingValue_eq (q : ℚ) (nonnegative : 0 ≤ q) : ceilingValue q = Nat.ceil q := by
  have numerator : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by
    have cast := congrArg (fun value : ℤ => (value : ℚ))
      (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr nonnegative))
    simpa only [Int.cast_natCast] using cast
  have fraction : ((q.num.natAbs : ℕ) : ℚ) / (q.den : ℚ) = q := by
    rw [numerator, Rat.num_div_den]
  have exactCeiling := ceil_nat_ratio q.num.natAbs q.den q.den_pos
  rw [fraction] at exactCeiling
  exact exactCeiling.symm

theorem Q_first_argument_pos (D : CertificateInput) :
    0 < (((D.M : ℚ) + 1) / D.gamma) :=
  div_pos (by positivity) D.gamma_pos

theorem Q_second_argument_pos (D : CertificateInput) :
    0 < ((2 * (D.E : ℚ)) / D.gamma ^ 2) := by
  have positive : 0 < D.E := lt_of_lt_of_le (by decide : 0 < 1) D.E_spec.1
  exact div_pos (by positivity) (sq_pos_of_pos D.gamma_pos)

theorem Q_eq_ceilingValue (D : CertificateInput) :
    D.Q = max 1 (max (ceilingValue (((D.M : ℚ) + 1) / D.gamma))
      (ceilingValue ((2 * (D.E : ℚ)) / D.gamma ^ 2))) := by
  rw [ceilingValue_eq _ (Q_first_argument_pos D).le,
    ceilingValue_eq _ (Q_second_argument_pos D).le]
  rfl

end PDROC.D27Prepare.Search
