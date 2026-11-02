module

public import Paid.PDCompute_SolverFieldBits_151

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits

def solverStatsBits (P : Parameters) (fee : ℚ) (n : ℕ) : ℕ :=
  2*((n+1)*(2*(P.certificate.M+1)+2)*maximumMenuBits P fee)+64*(maximumMenuBits P fee+natBits n+1)+2

/-- EXACT original standalone scalar in UniformRationalImplementationClaims. -/
def solverBitScale (P : Parameters) (fee penalty : ℚ) (n k : ℕ) : ℕ :=
  (n+1)*(2*(P.certificate.M+1)+2)*(maximumMenuBits P fee+1)+ratEncodingBits penalty+natBits n+natBits k+1

theorem solverStatsBudget_arith (A L T u v : ℕ) (positive : 1≤A) :
    2*(A*L)+64*(L+u+1)+2 ≤ 256*(A*(L+1)+T+u+v+1) := by
  have mulL : L≤A*L := by simpa only [one_mul] using Nat.mul_le_mul_right L positive
  nlinarith

theorem solverStatsBits_le_scale (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    solverStatsBits P fee n ≤ 256*solverBitScale P fee penalty n k := by
  have positive : 1≤(n+1)*(2*(P.certificate.M+1)+2) := by nlinarith
  exact solverStatsBudget_arith _ _ _ _ _ positive

/-- A SINGLE constant multiple of the original scale pays all real
fixed-depth DP arithmetic guards. There is no row/M multiplier on T. -/
theorem solverNumericGuard_arith (scale S L T : ℕ) (positive : 1≤scale)
    (stats : S≤256*scale) (data : L≤scale) (penalty : T≤scale) :
    1+16*(S+L+T+1)≤4194304*scale ∧
    1+16*(2*(S+3)+L+T+1)≤4194304*scale ∧
    1+64*(L+16*(2*(S+3)+L+T+1)+1)≤4194304*scale ∧
    1+64*(L+2*(S+3)+1)≤4194304*scale := by omega

theorem solverBitScale_positive (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    1≤solverBitScale P fee penalty n k := by unfold solverBitScale; omega

theorem solverBitScale_data (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    maximumMenuBits P fee≤solverBitScale P fee penalty n k := by
  have positive : 1≤(n+1)*(2*(P.certificate.M+1)+2) := by nlinarith
  have bound := Nat.mul_le_mul_right (maximumMenuBits P fee+1) positive
  simp only [one_mul] at bound
  unfold solverBitScale
  omega

theorem solverBitScale_penalty (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    ratEncodingBits penalty≤solverBitScale P fee penalty n k := by unfold solverBitScale; omega

theorem solverNumericGuard_original (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    1+16*(solverStatsBits P fee n+maximumMenuBits P fee+ratEncodingBits penalty+1)≤4194304*solverBitScale P fee penalty n k ∧
    1+16*(2*(solverStatsBits P fee n+3)+maximumMenuBits P fee+ratEncodingBits penalty+1)≤4194304*solverBitScale P fee penalty n k ∧
    1+64*(maximumMenuBits P fee+16*(2*(solverStatsBits P fee n+3)+maximumMenuBits P fee+ratEncodingBits penalty+1)+1)≤4194304*solverBitScale P fee penalty n k ∧
    1+64*(maximumMenuBits P fee+2*(solverStatsBits P fee n+3)+1)≤4194304*solverBitScale P fee penalty n k :=
  solverNumericGuard_arith _ _ _ _ (solverBitScale_positive P fee penalty n k) (solverStatsBits_le_scale P fee penalty n k)
    (solverBitScale_data P fee penalty n k) (solverBitScale_penalty P fee penalty n k)

end PDCompute.Solver
