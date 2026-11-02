module

public import RootB234_ECost_Total004
public import RootB23_PrepScalarPublic_001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.ECost

open PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation RootB234.PrepExponent

/-- Pure internal cost absorption. The four bounds concern the actual
caller's physical entry and original N. They are not added to original
controller eligibility. The computed E bound is discharged here using the
frozen original PrepScalar theorem, rather than supplied by the caller. -/
theorem original_scale_consumer (coefficient degree : Nat) :
    ∃ c d : Nat, 0 < c ∧ 0 < d ∧
      ∀ (I : Instance) (input : StatisticalInput I) (contract : Contract I) (budget : Rat)
        (background : Bank) (tail : List Bool),
        RatInput.occupied background ≤ coefficient*(arithmeticScale input contract budget)^degree →
        tail.length ≤ coefficient*(arithmeticScale input contract budget)^degree →
        field budget ≤ coefficient*(arithmeticScale input contract budget)^degree →
        I.stageCount ≤ coefficient*(arithmeticScale input contract budget)^degree →
        Global.totalCost background tail budget I.stageCount ≤ c*(arithmeticScale input contract budget)^d := by
  refine ⟨totalCoefficient*(4*coefficient+2)^5,(degree+1)*5,?_,by omega,?_⟩
  · apply Nat.mul_pos totalCoefficient_pos
    exact Nat.pow_pos (by omega)
  · intro I input contract budget background tail massBound tailBound budgetBound numberBound
    let S := arithmeticScale input contract budget
    let H := S^(degree+1)
    have positive : 1 ≤ S := by unfold S arithmeticScale; omega
    have power : S^degree ≤ H := Nat.pow_le_pow_right positive (Nat.le_succ degree)
    have scalar : S ≤ H := by
      simpa only [pow_one] using Nat.pow_le_pow_right positive (show 1 ≤ degree+1 by omega)
    have one : 1 ≤ H := positive.trans scalar
    have mass := massBound.trans (Nat.mul_le_mul_left coefficient power)
    have tailSize := tailBound.trans (Nat.mul_le_mul_left coefficient power)
    have bits := budgetBound.trans (Nat.mul_le_mul_left coefficient power)
    have number := numberBound.trans (Nat.mul_le_mul_left coefficient power)
    have computed := RootB23.PrepScalar.original_global_exponent_bounded I input contract budget
    have target : Global.targetExponent budget I.stageCount ≤ H := by
      have original : Global.targetExponent budget I.stageCount ≤ S := by
        simpa only [Global.targetExponent,computedExponent] using computed
      exact original.trans scalar
    have bounded : Global.resourceScale background tail budget I.stageCount ≤
        (4*coefficient+2)*H := by
      change RatInput.occupied background+tail.length+field budget+I.stageCount+
        Global.targetExponent budget I.stageCount+1 ≤ _
      nlinarith only [mass,tailSize,bits,number,target,one]
    have rawCost := total_cost background tail budget I.stageCount
    exact rawCost.trans ((Nat.mul_le_mul_left totalCoefficient (Nat.pow_le_pow_left bounded 5)).trans_eq (by
      dsimp only [H,S]
      rw [mul_pow,←pow_mul]
      ring))

end RootB234.ECost
