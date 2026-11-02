module

public import PaperProofs.Paid.PDROC_DataBits_011
public import PaperProofs.Paid.ComputationalClaims

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits

namespace PDROC.D27Prepare.Resources

abbrev Input := Parameters × ℚ

def size (x : Input) : ℕ := variableGammaSize x.1 x.2

theorem size_pos (x : Input) : 1 ≤ size x := by
  unfold size variableGammaSize rawSize
  omega

theorem fullInputSize_le_size (x : Input) : fullInputSize x ≤ size x := by
  unfold fullInputSize size variableGammaSize rawSize
  omega

theorem polynomial_of_fullInputSize {value : Input → ℕ}
    (h : PolynomialBound fullInputSize value) : PolynomialBound size value := by
  obtain ⟨C, d, hC, hv⟩ := h
  exact ⟨C, d, hC, fun x => (hv x).trans
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (fullInputSize_le_size x) d))⟩

theorem numericalSize_polynomial : PolynomialBound size (fun x => x.1.numericalSize x.2) :=
  polynomial_of_fullInputSize PDROC.DataBits.numericalSize_polynomial

def countWeight (P : Parameters) : ℕ :=
  P.certificate.t0 + P.certificate.M + P.certificate.E + P.certificate.Q

/-- E is included explicitly: it is not a summand of original numericalSize. -/
theorem countWeight_le (P : Parameters) (fee : ℚ) :
    countWeight P ≤ 128 * (variableGammaSize P fee) ^ 8 := by
  have h := certificate_counts_bound P.certificate
  have hs : dataInputSize P.certificate ≤ variableGammaSize P fee := by
    unfold dataInputSize variableGammaSize rawSize
    omega
  exact h.trans (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left hs 8))

theorem counts_polynomial : PolynomialBound size (fun x => countWeight x.1) :=
  ⟨128, 8, by decide, fun x => countWeight_le x.1 x.2⟩

theorem rational_add_polynomial {f g : Input → ℚ}
    (hf : PolynomialBound size (fun x => ratEncodingBits (f x)))
    (hg : PolynomialBound size (fun x => ratEncodingBits (g x))) :
    PolynomialBound size (fun x => ratEncodingBits (f x + g x)) :=
  ((PolynomialBound.constant size 2).mul (hf.add hg size_pos)).mono
    (fun x => ratEncodingBits_add_le (f x) (g x))

theorem rational_sub_polynomial {f g : Input → ℚ}
    (hf : PolynomialBound size (fun x => ratEncodingBits (f x)))
    (hg : PolynomialBound size (fun x => ratEncodingBits (g x))) :
    PolynomialBound size (fun x => ratEncodingBits (f x - g x)) :=
  ((PolynomialBound.constant size 2).mul (hf.add hg size_pos)).mono
    (fun x => ratEncodingBits_sub_le (f x) (g x))

theorem rational_mul_polynomial {f g : Input → ℚ}
    (hf : PolynomialBound size (fun x => ratEncodingBits (f x)))
    (hg : PolynomialBound size (fun x => ratEncodingBits (g x))) :
    PolynomialBound size (fun x => ratEncodingBits (f x * g x)) :=
  (hf.add hg size_pos).mono (fun x => ratEncodingBits_mul_le (f x) (g x))

theorem rational_div_polynomial {f g : Input → ℚ}
    (hf : PolynomialBound size (fun x => ratEncodingBits (f x)))
    (hg : PolynomialBound size (fun x => ratEncodingBits (g x))) :
    PolynomialBound size (fun x => ratEncodingBits (f x / g x)) :=
  (hf.add hg size_pos).mono (fun x => ratEncodingBits_div_le (f x) (g x))

theorem rational_pow_polynomial {f : Input → ℚ} {n : Input → ℕ}
    (hf : PolynomialBound size (fun x => ratEncodingBits (f x)))
    (hn : PolynomialBound size n) :
    PolynomialBound size (fun x => ratEncodingBits (f x ^ n x)) :=
  ((hn.add (PolynomialBound.constant size 1) size_pos).mul
    (hf.add (PolynomialBound.constant size 1) size_pos)).mono
    (fun x => ratEncodingBits_pow_le (f x) (n x))

theorem rational_natCast_polynomial {n : Input → ℕ} (hn : PolynomialBound size n) :
    PolynomialBound size (fun x => ratEncodingBits (n x : ℚ)) := by
  apply ((PolynomialBound.natBits size_pos hn).add (PolynomialBound.constant size 2) size_pos).mono
  intro x
  exact (ratEncodingBits_natCast (n x)).le

def originalRatio (P : Parameters) (fee : ℚ) : ℚ :=
  2 * P.Lambda * P.certificate.risk / P.positiveValueFloor fee

/-- A data-only envelope for original counts and exact scalar encodings.
Its polynomial theorem is not a runtime or final preparation claim. -/
def dataWeight (P : Parameters) (fee : ℚ) : ℕ :=
  variableGammaSize P fee + countWeight P + P.numericalSize fee +
    ratEncodingBits P.Lambda + ratEncodingBits (P.zeroChargeRisk fee) +
    ratEncodingBits (P.firstChargeFloor fee) + ratEncodingBits (P.positiveValueFloor fee) +
    ratEncodingBits (originalRatio P fee) + 64

theorem dataWeight_polynomial : PolynomialBound size (fun x => dataWeight x.1 x.2) := by
  have hs := PolynomialBound.size size
  have hT : PolynomialBound size (fun x => x.1.certificate.t0) :=
    counts_polynomial.mono (by intro x; unfold countWeight; omega)
  have hbT := PolynomialBound.natBits size_pos hT
  let c (n : ℕ) := PolynomialBound.constant size n
  have hLambda : PolynomialBound size (fun x => ratEncodingBits x.1.Lambda) := by
    apply ((hs.add hbT size_pos).add (c 10) size_pos).mono
    intro x
    have h := Lambda_encoding x.1
    unfold size variableGammaSize rawSize
    omega
  have hZeta : PolynomialBound size (fun x => ratEncodingBits (x.1.zeroChargeRisk x.2)) := by
    apply (((c 2).mul hs).add (c 3) size_pos).mono
    intro x
    have h := zeroChargeRisk_encoding x.1 x.2
    unfold size variableGammaSize rawSize
    omega
  have hFloor : PolynomialBound size (fun x => ratEncodingBits (x.1.firstChargeFloor x.2)) := by
    apply hs.mono
    intro x
    have h := firstChargeFloor_encoding x.1 x.2
    unfold size variableGammaSize rawSize
    omega
  have hRisk : PolynomialBound size (fun x => ratEncodingBits x.1.certificate.risk) :=
    hs.mono (by intro x; unfold size variableGammaSize rawSize; omega)
  have hGap := rational_sub_polynomial hZeta hRisk
  have hPositiveFloor : PolynomialBound size (fun x => ratEncodingBits (x.1.positiveValueFloor x.2)) :=
    rational_mul_polynomial hFloor hGap
  have hRatio : PolynomialBound size (fun x => ratEncodingBits (originalRatio x.1 x.2)) := by
    apply ((c 64).mul ((hs.add hbT size_pos).add (c 1) size_pos)).mono
    intro x
    have h := bisectionArgument_encoding x.1 x.2
    unfold originalRatio size variableGammaSize rawSize
    omega
  exact ((((((((hs.add counts_polynomial size_pos).add numericalSize_polynomial size_pos).add hLambda size_pos).add
    hZeta size_pos).add hFloor size_pos).add hPositiveFloor size_pos).add hRatio size_pos).add (c 64) size_pos)

theorem power_encoding_le (q : ℚ) (j bound : ℕ) (hj : j ≤ bound) :
    ratEncodingBits (q ^ j) ≤ (bound + 1) * (ratEncodingBits q + 1) :=
  (ratEncodingBits_pow_le q j).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hj 1))

theorem numeratorAbs_cell_bits (q : ℚ) :
    (Cell.natural q.num.natAbs).bits ≤ ratEncodingBits q + 1 := by
  change 1 + natBits q.num.natAbs ≤ ratEncodingBits q + 1
  unfold ratEncodingBits ratNumBits
  omega

theorem denominator_cell_bits (q : ℚ) :
    (Cell.natural q.den).bits ≤ ratEncodingBits q + 1 := by
  change 1 + natBits q.den ≤ ratEncodingBits q + 1
  unfold ratEncodingBits ratDenBits
  omega

/-- The ceil can be numerically enormous; its bit length remains bounded
by the exact original rational encoding, including q≤0 and q=0. -/
theorem ceil_cell_bits (q : ℚ) :
    (Cell.natural ⌈q⌉₊).bits ≤ ratEncodingBits q + 1 := by
  have hc : ⌈q⌉₊ ≤ q.num.natAbs := Nat.ceil_le.mpr (rat_le_numAbs q)
  exact (Nat.add_le_add_left (natBits_mono hc) 1).trans (numeratorAbs_cell_bits q)

end PDROC.D27Prepare.Resources
