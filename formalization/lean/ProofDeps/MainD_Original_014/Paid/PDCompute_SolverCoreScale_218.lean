module

public import Paid.PDCompute_SolverNumericScale_162

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits

/-- Original standalone DP scale at the genuine core dimensions, with
arbitrary penalty bit length still ADDITIVE. No source-call/cost oracle. -/
theorem solverBitScale_core_additive (P : Parameters) (fee penalty : ℚ) :
    solverBitScale P fee penalty P.certificate.stages P.tools≤
      2*coreOperandBound P fee+ratEncodingBits penalty := by
  let A:=(P.certificate.stages+1)*(2*(P.certificate.M+1)+2)*(maximumMenuBits P fee+1)
  have first:=Nat.mul_le_mul_left (P.certificate.stages+1) (by omega : 1≤2*(P.certificate.M+1)+2)
  simp only [Nat.mul_one] at first
  have second:=Nat.mul_le_mul_left ((P.certificate.stages+1)*(2*(P.certificate.M+1)+2)) (by omega : 1≤maximumMenuBits P fee+1)
  simp only [Nat.mul_one] at second
  have stageWeight : P.certificate.stages+1≤A:=first.trans second
  have stageBits : natBits P.certificate.stages≤P.certificate.stages+1:=
    Nat.add_le_add_right (Nat.log2_le_self _) 1
  have toolsBits : natBits P.tools≤rawSize P fee := by unfold rawSize;omega
  have coreTerms : A+rawSize P fee+1≤coreOperandBound P fee := by
    unfold coreOperandBound
    dsimp only [A]
    omega
  change A+ratEncodingBits penalty+natBits P.certificate.stages+natBits P.tools+1≤_
  omega

theorem solverBitScale_core (P : Parameters) (fee penalty : ℚ) (Cpenalty : ℕ)
    (penaltyBits : ratEncodingBits penalty≤Cpenalty*coreOperandBound P fee) :
    solverBitScale P fee penalty P.certificate.stages P.tools≤(Cpenalty+2)*coreOperandBound P fee := by
  have bound:=solverBitScale_core_additive P fee penalty
  nlinarith

theorem solver_core_scalarRoom (P : Parameters) (fee penalty : ℚ) (Cpenalty : ℕ)
    (penaltyBits : ratEncodingBits penalty≤Cpenalty*coreOperandBound P fee) :
    4194304*solverBitScale P fee penalty P.certificate.stages P.tools≤
      (4194304*(Cpenalty+2))*coreOperandBound P fee := by
  calc
    _≤4194304*((Cpenalty+2)*coreOperandBound P fee):=
      Nat.mul_le_mul_left 4194304 (solverBitScale_core P fee penalty Cpenalty penaltyBits)
    _=(4194304*(Cpenalty+2))*coreOperandBound P fee:=by ring

theorem solver_core_endpointCount_bits (P : Parameters) (fee : ℚ) :
    1+natBits (P.certificate.M+1)≤coreOperandBound P fee := by
  let A:=(P.certificate.stages+1)*(2*(P.certificate.M+1)+2)*(maximumMenuBits P fee+1)
  have first:=Nat.mul_le_mul_right (2*(P.certificate.M+1)+2) (by omega : 1≤P.certificate.stages+1)
  simp only [Nat.one_mul] at first
  have second:=Nat.mul_le_mul_left ((P.certificate.stages+1)*(2*(P.certificate.M+1)+2)) (by omega : 1≤maximumMenuBits P fee+1)
  simp only [Nat.mul_one] at second
  have endpointWeight : 2*(P.certificate.M+1)+2≤A:=first.trans second
  have bits : natBits (P.certificate.M+1)≤P.certificate.M+1+1:=
    Nat.add_le_add_right (Nat.log2_le_self _) 1
  have coreTerms : A≤coreOperandBound P fee := by unfold coreOperandBound;dsimp only [A];omega
  omega

end PDCompute.Solver
