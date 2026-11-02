module

public import PaperProofs.Paid.PDROC_DataBits_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

def PolynomialBound {X : Type*} (size value : X → ℕ) : Prop :=
  ∃ C degree : ℕ, 0 < C ∧ ∀ x, value x ≤ C * size x ^ degree

namespace PolynomialBound

theorem constant {X : Type*} (size : X → ℕ) (n : ℕ) : PolynomialBound size (fun _ => n) := by
  exact ⟨n+1, 0, by omega, by intro x; simp⟩

theorem size {X : Type*} (size : X → ℕ) : PolynomialBound size size := by
  exact ⟨1, 1, by omega, by intro x; simp⟩

theorem mono {X : Type*} {size value smaller : X → ℕ}
    (h : PolynomialBound size value) (hle : ∀ x, smaller x ≤ value x) : PolynomialBound size smaller := by
  obtain ⟨C, degree, hC, h⟩ := h
  exact ⟨C, degree, hC, fun x => (hle x).trans (h x)⟩

theorem add {X : Type*} {size f g : X → ℕ}
    (hf : PolynomialBound size f) (hg : PolynomialBound size g) (hs : ∀ x, 1 ≤ size x) :
    PolynomialBound size (fun x => f x + g x) := by
  obtain ⟨C, d, hC, hf⟩ := hf
  obtain ⟨D, e, hD, hg⟩ := hg
  refine ⟨C+D, d+e, by omega, ?_⟩
  intro x
  have hd : 1 ≤ size x ^ d := one_le_pow₀ (hs x)
  have he : 1 ≤ size x ^ e := one_le_pow₀ (hs x)
  have hf' : C*size x^d ≤ C*size x^d*size x^e := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (C*size x^d) he
  have hg' : D*size x^e ≤ D*size x^d*size x^e := by
    have h := Nat.mul_le_mul_left (D*size x^e) hd
    simpa only [Nat.mul_one, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  calc
    f x + g x ≤ C*size x^d + D*size x^e := Nat.add_le_add (hf x) (hg x)
    _ ≤ C*size x^d*size x^e + D*size x^d*size x^e := Nat.add_le_add hf' hg'
    _ = (C+D)*size x^(d+e) := by rw [pow_add]; ring

theorem mul {X : Type*} {size f g : X → ℕ}
    (hf : PolynomialBound size f) (hg : PolynomialBound size g) :
    PolynomialBound size (fun x => f x * g x) := by
  obtain ⟨C, d, hC, hf⟩ := hf
  obtain ⟨D, e, hD, hg⟩ := hg
  refine ⟨C*D, d+e, Nat.mul_pos hC hD, ?_⟩
  intro x
  calc
    f x * g x ≤ (C*size x^d)*(D*size x^e) := Nat.mul_le_mul (hf x) (hg x)
    _ = C*D*size x^(d+e) := by rw [pow_add]; ring

theorem natBits {X : Type*} {size value : X → ℕ} (hs : ∀ x, 1 ≤ size x)
    (h : PolynomialBound size value) : PolynomialBound size (fun x => natBits (value x)) := by
  apply (add h (constant size 1) hs).mono
  intro x
  exact natBits_le_succ (value x)

end PolynomialBound

theorem fixedGammaPolynomialData_of_variable (gamma : ℚ) (h : VariableGammaPolynomialData) :
    FixedGammaPolynomialData gamma := by
  obtain ⟨C, degree, hC, h⟩ := h
  let A := ratEncodingBits gamma + ⌈gamma⁻¹⌉₊
  refine ⟨C*(A+1)^degree, degree, Nat.mul_pos hC (pow_pos (by omega) _), ?_⟩
  intro P fee hgamma hfee
  let S := P.certificate.stages + ratEncodingBits P.certificate.risk +
    ratEncodingBits P.reviewFee + ratEncodingBits fee + 1
  have hsize : P.certificate.stages + ratEncodingBits P.certificate.gamma +
      ratEncodingBits P.certificate.risk + ratEncodingBits P.reviewFee + ratEncodingBits fee +
      ⌈P.certificate.gamma⁻¹⌉₊ + 1 ≤ (A+1)*S := by
    rw [hgamma]
    dsimp [A, S]
    nlinarith
  calc
    P.numericalSize fee ≤ C*(P.certificate.stages + ratEncodingBits P.certificate.gamma +
        ratEncodingBits P.certificate.risk + ratEncodingBits P.reviewFee + ratEncodingBits fee +
        ⌈P.certificate.gamma⁻¹⌉₊ + 1)^degree := h P fee hfee
    _ ≤ C*((A+1)*S)^degree := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsize degree)
    _ = (C*(A+1)^degree)*S^degree := by rw [mul_pow]; ring

end PDROC.DataBits
