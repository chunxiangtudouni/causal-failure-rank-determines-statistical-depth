module

public import RootB234_ECost_Bounds003
public import RootB234_PrepExponent_GlobalResources042

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.ECost

open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM RootB234.PrepExponent

def mulCoefficient : Nat := binaryTimeCoefficient RatMulDiv.mulCoefficient*1024^4
def subCoefficient : Nat := binaryTimeCoefficient RatAddSub.addSubCoefficient*1024^4
def initialCoefficient : Nat := QLoop.fullCoefficient+3*mulCoefficient+100000000
def loopCoefficient : Nat := subCoefficient+mulCoefficient+3000
def totalCoefficient : Nat := initialCoefficient+loopCoefficient+1

theorem totalCoefficient_pos : 0 < totalCoefficient := by unfold totalCoefficient; omega

variable {background : Bank} {tail : List Bool} {budget : Rat} {number limit B : Nat}

theorem initial_cost (basis : Basis background tail budget number limit B) :
    Global.initialCost background tail budget number ≤ initialCoefficient*B^5 := by
  have h1 := binary_time_budget RatMulDiv.mulCoefficient background (qCache tail budget number) [] 2
    (number : Rat) (RatInput.Encoder.packet (Global.qValue number) []) B (first_binary_scale basis)
  have h2 := binary_time_budget RatMulDiv.mulCoefficient background (qCache tail budget number) []
    (2*(number : Rat)) (Global.qValue number) [] B (second_binary_scale basis)
  have h3 := binary_time_budget RatMulDiv.mulCoefficient background (rCache tail budget number) []
    2 budget [] B (third_binary_scale basis)
  have quartic : B^4 ≤ B^5 := Nat.pow_le_pow_right basis.positive (by decide : 4 ≤ 5)
  have linear : B ≤ B^5 := by simpa only [pow_one] using Nat.pow_le_pow_right basis.positive (show 1 ≤ 5 by decide)
  have one : 1 ≤ B^5 := one_le_pow₀ basis.positive
  have a1 := h1.trans (Nat.mul_le_mul_left mulCoefficient quartic)
  have a2 := h2.trans (Nat.mul_le_mul_left mulCoefficient quartic)
  have a3 := h3.trans (Nat.mul_le_mul_left mulCoefficient quartic)
  have natScale := (initial_nat_scale basis).trans (Nat.mul_le_mul_left 1000000 linear)
  have q := (q_width basis).trans (Nat.mul_le_mul_left 5 linear)
  have r := (r_width basis).trans (Nat.mul_le_mul_left 10 linear)
  have b := basis.budgetBound.trans linear
  have doubled := (twice_budget_width basis).trans (Nat.mul_le_mul_left 4 linear)
  have scaleBound : QLoop.fullScale background tail budget number ≤ B := basis.initial
  have qLoop := Nat.mul_le_mul_left QLoop.fullCoefficient (Nat.pow_le_pow_left scaleBound 5)
  change QLoop.fullCoefficient*(QLoop.fullScale background tail budget number)^5+
    13*NatToRat.scale (Global.bank background (qCache tail budget number) [] [] [] [] []) number
      (RatInput.Encoder.packet (Global.qValue number) [])+
    RatBinary.time RatMulDiv.mulCoefficient (QLoop.rawBackground background (qCache tail budget number) [])
      2 (number : Rat) (RatInput.Encoder.packet (Global.qValue number) []) (qCache tail budget number)+
    RatBinary.time RatMulDiv.mulCoefficient (QLoop.rawBackground background (qCache tail budget number) [])
      (2*(number : Rat)) (Global.qValue number) [] (qCache tail budget number)+
    RatBinary.time RatMulDiv.mulCoefficient (QLoop.rawBackground background (rCache tail budget number) [])
      2 budget [] (rCache tail budget number)+
    40*(field (Global.qValue number)+field (Global.rValue number)+field budget+field (2*budget))+1000 ≤ _
  unfold initialCoefficient
  nlinarith only [a1,a2,a3,natScale,q,r,b,doubled,qLoop,one]

theorem compare_cost (basis : Basis background tail budget number limit B) (exponent : Nat) (within : exponent ≤ limit) :
    Global.compareCost background (qCache tail budget number)
      (B23_4_RatWordPrep.NatField.packet exponent []) (Global.rValue number) (Global.yValue budget exponent) ≤
        (subCoefficient+1000)*B^4 := by
  have arithmetic := binary_time_budget RatAddSub.addSubCoefficient background (loopCache tail budget number exponent)
    (B23_4_RatWordPrep.NatField.packet exponent []) (Global.rValue number) (Global.yValue budget exponent) [] B
    (compare_binary_scale basis exponent within)
  have linear : B ≤ B^4 := by simpa only [pow_one] using Nat.pow_le_pow_right basis.positive (show 1 ≤ 4 by decide)
  have one : 1 ≤ B^4 := one_le_pow₀ basis.positive
  have r := (r_width basis).trans (Nat.mul_le_mul_left 10 linear)
  have y := (y_width basis exponent within).trans (Nat.mul_le_mul_left 4 linear)
  have difference := sub_field (Global.rValue number) (Global.yValue budget exponent)
  change RatBinary.time RatAddSub.addSubCoefficient (QLoop.rawBackground background (loopCache tail budget number exponent)
    (B23_4_RatWordPrep.NatField.packet exponent [])) (Global.rValue number) (Global.yValue budget exponent) []
      (loopCache tail budget number exponent)+9*field (Global.yValue budget exponent)+
      3*field (Global.rValue number)+field (Global.rValue number-Global.yValue budget exponent)+63 ≤ _
  change _ ≤ subCoefficient*B^4 at arithmetic
  nlinarith only [arithmetic,r,y,difference,one]

theorem repeat_cost (basis : Basis background tail budget number limit B) (exponent : Nat) (within : exponent ≤ limit) :
    Global.repeatCost background (qCache tail budget number) (Global.rValue number)
      (Global.yValue budget exponent) exponent ≤ (mulCoefficient+1000)*B^4 := by
  have arithmetic := binary_time_budget RatMulDiv.mulCoefficient background (loopCache tail budget number exponent)
    (B23_4_RatWordPrep.NatField.packet exponent []) 2 (Global.yValue budget exponent) [] B
    (repeat_binary_scale basis exponent within)
  change _ ≤ mulCoefficient*B^4 at arithmetic
  have linear : B ≤ B^4 := by simpa only [pow_one] using Nat.pow_le_pow_right basis.positive (show 1 ≤ 4 by decide)
  have one : 1 ≤ B^4 := one_le_pow₀ basis.positive
  have y := (y_width basis exponent within).trans (Nat.mul_le_mul_left 4 linear)
  have digits := (exponent_raw basis exponent within).trans linear
  have doubled := QLoop.double_field (Global.yValue budget exponent)
  change field (2*Global.yValue budget exponent) ≤ field (Global.yValue budget exponent)+3 at doubled
  change RatBinary.time RatMulDiv.mulCoefficient (QLoop.rawBackground background (loopCache tail budget number exponent)
    (B23_4_RatWordPrep.NatField.packet exponent [])) 2 (Global.yValue budget exponent) []
      (loopCache tail budget number exponent)+8*field (Global.yValue budget exponent)+
      3*field (2*Global.yValue budget exponent)+3*(raw exponent).length+55 ≤ _
  nlinarith only [arithmetic,y,digits,doubled,one]

theorem stop_cost (basis : Basis background tail budget number limit B) (exponent : Nat) (within : exponent ≤ limit) :
    Global.stopCost (Global.rValue number) (Global.yValue budget exponent) (Global.qValue number) budget ≤ 1000*B^4 := by
  have linear : B ≤ B^4 := by simpa only [pow_one] using Nat.pow_le_pow_right basis.positive (show 1 ≤ 4 by decide)
  have one : 1 ≤ B^4 := one_le_pow₀ basis.positive
  have r := (r_width basis).trans (Nat.mul_le_mul_left 10 linear)
  have q := (q_width basis).trans (Nat.mul_le_mul_left 5 linear)
  have y := (y_width basis exponent within).trans (Nat.mul_le_mul_left 4 linear)
  have b := basis.budgetBound.trans linear
  change 5*field (Global.yValue budget exponent)+5*field (Global.rValue number)+6*field (Global.qValue number)+
    3*field budget+86 ≤ _
  nlinarith only [r,q,y,b,one]

theorem loop_cost (basis : Basis background tail budget number limit B) (remaining exponent : Nat)
    (finish : exponent+remaining ≤ limit) :
    Global.loopCost background tail budget number remaining exponent ≤ loopCoefficient*(remaining+1)*B^4 := by
  induction remaining generalizing exponent with
  | zero =>
    have within : exponent ≤ limit := by omega
    have comparison := compare_cost basis exponent within
    have stopping := stop_cost basis exponent within
    dsimp only [qCache] at comparison
    change _+_ ≤ _
    unfold loopCoefficient
    nlinarith only [comparison,stopping,Nat.zero_le (mulCoefficient*B^4),Nat.zero_le (B^4)]
  | succ remaining ih =>
    have within : exponent ≤ limit := by omega
    have next : exponent+1+remaining ≤ limit := by omega
    have comparison := compare_cost basis exponent within
    have repeated := repeat_cost basis exponent within
    dsimp only [qCache] at comparison repeated
    have later := ih (exponent+1) next
    rw [Global.loopCost]
    change _+_+_ ≤ _
    unfold loopCoefficient at later ⊢
    nlinarith only [comparison,repeated,later,Nat.zero_le (B^4)]

theorem total_cost (background : Bank) (tail : List Bool) (budget : Rat) (number : Nat) :
    Global.totalCost background tail budget number ≤
      totalCoefficient*(Global.resourceScale background tail budget number)^5 := by
  let E := Global.targetExponent budget number
  let B := Global.resourceScale background tail budget number
  have basis := potential_basis background tail budget number E
  change Basis background tail budget number E B at basis
  have initial := initial_cost basis
  change Global.initialCost background tail budget number ≤ initialCoefficient*B^5 at initial
  have positive : 1 ≤ E := by
    unfold E Global.targetExponent PaperProofs.Statistics.BinaryExperiment.quotaExponent
    exact le_max_left _ _
  have finish : 1+(E-1) ≤ E := by omega
  have loop := loop_cost basis (E-1) 1 finish
  change Global.loopCost background tail budget number (E-1) 1 ≤ loopCoefficient*(E-1+1)*B^4 at loop
  have count : E-1+1 ≤ B := by have bound := basis.limitBound; omega
  have loopBound : Global.loopCost background tail budget number (E-1) 1 ≤ loopCoefficient*B^5 := by
    exact loop.trans ((Nat.mul_le_mul_right (B^4) (Nat.mul_le_mul_left loopCoefficient count)).trans_eq (by ring))
  change Global.initialCost background tail budget number+Global.loopCost background tail budget number (E-1) 1 ≤ totalCoefficient*B^5
  unfold totalCoefficient
  nlinarith only [initial,loopBound,Nat.zero_le (B^5)]

theorem fixed_polynomial :
    ∃ c d : Nat, 0 < c ∧ 0 < d ∧ ∀ (background : Bank) (tail : List Bool) (budget : Rat) (number : Nat),
      Global.totalCost background tail budget number ≤
        c*(RatInput.occupied background+tail.length+field budget+number+Global.targetExponent budget number+1)^d := by
  exact ⟨totalCoefficient,5,totalCoefficient_pos,by decide,fun background tail budget number =>
    total_cost background tail budget number⟩

end RootB234.ECost
