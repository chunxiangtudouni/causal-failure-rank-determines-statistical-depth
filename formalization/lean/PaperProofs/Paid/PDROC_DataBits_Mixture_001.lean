module

public import PaperProofs.Paid.PDROC_DataBits_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid.Parameters

namespace PDROC.DataBits

theorem rat_numAbs_divInt_le (a b : ℤ) (hb : b ≠ 0) :
    (Rat.divInt a b).num.natAbs ≤ a.natAbs := by
  by_cases ha : a = 0
  · simp [ha]
  · exact Nat.le_of_dvd (Int.natAbs_pos.mpr ha)
      (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd a hb))

theorem rat_den_divInt_le (a b : ℤ) (hb : b ≠ 0) : (Rat.divInt a b).den ≤ b.natAbs :=
  Nat.le_of_dvd (Int.natAbs_pos.mpr hb) (Int.ofNat_dvd_left.mp (Rat.den_dvd a b))

theorem ratNumAbs_add_le (x y : ℚ) :
    (x + y).num.natAbs ≤ x.num.natAbs * y.den + x.den * y.num.natAbs := by
  rw [Rat.add_num_den x y]
  have hd : (x.den : ℤ) * (y.den : ℤ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast x.den_nz) (by exact_mod_cast y.den_nz)
  have hn := rat_numAbs_divInt_le (x.num * y.den + x.den * y.num)
    ((x.den : ℤ) * (y.den : ℤ)) hd
  have ha : (x.num * y.den + x.den * y.num : ℤ).natAbs ≤
      x.num.natAbs * y.den + x.den * y.num.natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
      Int.natAbs_add_le (x.num * y.den) (x.den * y.num)
  exact hn.trans ha

theorem ratDen_add_le (x y : ℚ) : (x + y).den ≤ x.den * y.den :=
  Nat.le_of_dvd (Nat.mul_pos x.den_pos y.den_pos) (Rat.add_den_dvd x y)

theorem ratNumAbs_mul_le (x y : ℚ) : (x * y).num.natAbs ≤ x.num.natAbs * y.num.natAbs := by
  rw [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt]
  have hd : ((x.den * y.den : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero x.den_nz y.den_nz
  simpa only [Int.natAbs_mul] using rat_numAbs_divInt_le (x.num * y.num) ((x.den * y.den : ℕ) : ℤ) hd

theorem ratDen_mul_le (x y : ℚ) : (x * y).den ≤ x.den * y.den :=
  Nat.le_of_dvd (Nat.mul_pos x.den_pos y.den_pos) (Rat.mul_den_dvd x y)

theorem ratNumBits_add_le (x y : ℚ) :
    ratNumBits (x + y) ≤ ratNumBits x + ratDenBits y + ratDenBits x + ratNumBits y := by
  apply (natBits_mono (ratNumAbs_add_le x y)).trans
  simpa only [ratNumBits, ratDenBits, Nat.add_assoc] using
    (natBits_add_le (x.num.natAbs * y.den) (x.den * y.num.natAbs)).trans
      (Nat.add_le_add (natBits_mul_le _ _) (natBits_mul_le _ _))

theorem ratDenBits_add_le (x y : ℚ) : ratDenBits (x + y) ≤ ratDenBits x + ratDenBits y :=
  (natBits_mono (ratDen_add_le x y)).trans (natBits_mul_le _ _)

theorem ratNumBits_mul_le (x y : ℚ) : ratNumBits (x * y) ≤ ratNumBits x + ratNumBits y :=
  (natBits_mono (ratNumAbs_mul_le x y)).trans (natBits_mul_le _ _)

theorem ratDenBits_mul_le (x y : ℚ) : ratDenBits (x * y) ≤ ratDenBits x + ratDenBits y :=
  (natBits_mono (ratDen_mul_le x y)).trans (natBits_mul_le _ _)

theorem ratNumBits_inv (q : ℚ) : ratNumBits q⁻¹ = ratDenBits q := by
  by_cases hq : q = 0
  · subst q
    norm_num [ratNumBits, ratDenBits, natBits]
  · have hn : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
    simp only [ratNumBits, ratDenBits, Rat.num_inv, Int.natAbs_mul,
      Int.natAbs_sign_of_ne_zero hn, Int.natAbs_natCast, one_mul]

theorem ratDenBits_inv (q : ℚ) : ratDenBits q⁻¹ = ratNumBits q := by
  by_cases hq : q = 0
  · subst q
    norm_num [ratNumBits, ratDenBits, natBits]
  · have hn : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
    simp only [ratDenBits, ratNumBits, Rat.den_inv, ite_eq_right hn]

theorem ratEncodingBits_inv (q : ℚ) : ratEncodingBits q⁻¹ = ratEncodingBits q := by
  unfold ratEncodingBits
  rw [ratNumBits_inv, ratDenBits_inv]
  omega

theorem ratEncodingBits_neg (q : ℚ) : ratEncodingBits (-q) = ratEncodingBits q := by
  simp only [ratEncodingBits, ratNumBits, ratDenBits, Rat.neg_num, Rat.neg_den, Int.natAbs_neg]

theorem ratEncodingBits_add_le (x y : ℚ) :
    ratEncodingBits (x + y) ≤ 2 * (ratEncodingBits x + ratEncodingBits y) := by
  have hn := ratNumBits_add_le x y
  have hd := ratDenBits_add_le x y
  unfold ratEncodingBits
  omega

theorem ratEncodingBits_sub_le (x y : ℚ) :
    ratEncodingBits (x - y) ≤ 2 * (ratEncodingBits x + ratEncodingBits y) := by
  simpa only [sub_eq_add_neg, ratEncodingBits_neg] using ratEncodingBits_add_le x (-y)

theorem ratEncodingBits_mul_le (x y : ℚ) :
    ratEncodingBits (x * y) ≤ ratEncodingBits x + ratEncodingBits y := by
  have hn := ratNumBits_mul_le x y
  have hd := ratDenBits_mul_le x y
  unfold ratEncodingBits
  omega

theorem ratEncodingBits_div_le (x y : ℚ) :
    ratEncodingBits (x / y) ≤ ratEncodingBits x + ratEncodingBits y := by
  simpa only [div_eq_mul_inv, ratEncodingBits_inv] using ratEncodingBits_mul_le x y⁻¹

theorem ratNumBits_pow_le (q : ℚ) (n : ℕ) : ratNumBits (q ^ n) ≤ n * ratNumBits q + 1 := by
  simpa only [ratNumBits, Rat.num_pow, Int.natAbs_pow] using natBits_pow_le q.num.natAbs n

theorem ratDenBits_pow_le (q : ℚ) (n : ℕ) : ratDenBits (q ^ n) ≤ n * ratDenBits q + 1 := by
  simpa only [ratDenBits, Rat.den_pow] using natBits_pow_le q.den n

theorem ratEncodingBits_pow_le (q : ℚ) (n : ℕ) :
    ratEncodingBits (q ^ n) ≤ (n + 1) * (ratEncodingBits q + 1) := by
  have hn := ratNumBits_pow_le q n
  have hd := ratDenBits_pow_le q n
  have hn0 := natBits_pos q.num.natAbs
  have hd0 := natBits_pos q.den
  change 0 < ratNumBits q at hn0
  change 0 < ratDenBits q at hd0
  unfold ratEncodingBits
  nlinarith

theorem ratNumAbs_le_den (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : q.num.natAbs ≤ q.den := by
  have hn0 : 0 ≤ q.num := Rat.num_nonneg.mpr h0
  have hfrac : (q.num : ℚ) / (q.den : ℚ) ≤ 1 := by rw [Rat.num_div_den]; exact h1
  have hnq : (q.num : ℚ) ≤ (q.den : ℚ) :=
    (div_le_one (by exact_mod_cast q.den_pos)).mp hfrac
  have hn : q.num ≤ (q.den : ℤ) := by exact_mod_cast hnq
  have ha : (q.num.natAbs : ℤ) ≤ (q.den : ℤ) :=
    (Int.natAbs_of_nonneg hn0).trans_le hn
  exact_mod_cast ha

theorem ratNumBits_le_ratDenBits (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ratNumBits q ≤ ratDenBits q := natBits_mono (ratNumAbs_le_den q h0 h1)

end PDROC.DataBits
