module

public import Paid.PDROC_BitVM_Link_Joined_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Size

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

/-- Once gamma is fixed this coefficient is a constant, while the SAME
machine remains chosen before every gamma/instance/fee. -/
def fixedFactor (gamma : ℚ) : ℕ := ratEncodingBits gamma + ⌈gamma⁻¹⌉₊ + 2

theorem factor_positive (gamma : ℚ) : 0 < fixedFactor gamma := by
  unfold fixedFactor
  omega

theorem raw_positive (P : PaperProofs.Paid.Parameters) (fee : ℚ) : 1 ≤ rawSize P fee := by
  unfold rawSize
  omega

theorem variable_le_fixed (gamma : ℚ) (P : PaperProofs.Paid.Parameters) (fee : ℚ)
    (same : P.certificate.gamma=gamma) :
    variableGammaSize P fee ≤ fixedFactor gamma * rawSize P fee := by
  have positive := raw_positive P fee
  simp only [variableGammaSize,fixedFactor,same]
  nlinarith

theorem polynomial_fixed (C degree : ℕ) (gamma : ℚ)
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (same : P.certificate.gamma=gamma) :
    C*(variableGammaSize P fee)^degree ≤ 
      (C*(fixedFactor gamma)^degree)*(rawSize P fee)^degree := by
  calc
    C*(variableGammaSize P fee)^degree ≤ C*(fixedFactor gamma*rawSize P fee)^degree :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left (variable_le_fixed gamma P fee same) degree)
    _ = (C*(fixedFactor gamma)^degree)*(rawSize P fee)^degree := by rw [mul_pow,Nat.mul_assoc]

/-- Conditional assembly bridge for the ORIGINAL D27 quantifiers. This
does not provide a runtime oracle: the hypothesis must be the full actual
raw-input Bool run. A single uniform variable-gamma proof gives both clauses,
without choosing a new machine after seeing gamma. -/
theorem claims_of_variable (states : ℕ) (machine : BitMachine states) (C degree : ℕ)
    (positive : 0 < C)
    (actual : ∀ (P : PaperProofs.Paid.Parameters) (fee : ℚ),0 ≤ fee → 
      ∃ trace final,BitRuns machine (encodeBits (rawInput P fee)) trace final ∧ 
        final.Tape.right₀=Turing.ListBlank.mk (encodeBits (encodeArtifact (buildArtifact P fee))) ∧ 
        trace.length ≤ C*(variableGammaSize P fee)^degree ∧ 
        visitedBitSpace machine (encodeBits (rawInput P fee)).length trace ≤ 
          C*(variableGammaSize P fee)^degree) : UniformBitImplementationClaims := by
  refine ⟨states,machine,?_,C,degree,positive,actual⟩
  intro gamma _gammaPositive _gammaSmall
  refine ⟨C*(fixedFactor gamma)^degree,degree,Nat.mul_pos positive (pow_pos (factor_positive gamma) _),?_⟩
  intro P fee same feeNonnegative
  obtain ⟨trace,final,run,output,time,space⟩ := actual P fee feeNonnegative
  have bound := polynomial_fixed C degree gamma P fee same
  exact ⟨trace,final,run,output,time.trans bound,space.trans bound⟩

end PDROC.BitVM.Size
