module

public import RootB234_ECost_Arithmetic002

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.ECost

open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM RootB234.PrepExponent

def potential (background : Bank) (tail : List Bool) (budget : Rat) (number limit : Nat) : Nat :=
  RatInput.occupied background+tail.length+field budget+number+limit+1

structure Basis (background : Bank) (tail : List Bool) (budget : Rat) (number limit B : Nat) : Prop where
  positive : 1 ≤ B
  massBound : RatInput.occupied background ≤ B
  tailBound : tail.length ≤ B
  budgetBound : field budget ≤ B
  numberBound : number+1 ≤ B
  limitBound : limit+1 ≤ B
  initial : QLoop.fullScale background tail budget number ≤ B

theorem potential_basis (background : Bank) (tail : List Bool) (budget : Rat) (number limit : Nat) :
    Basis background tail budget number limit (potential background tail budget number limit) := by
  constructor <;> dsimp only [potential,QLoop.fullScale,field] <;> omega

def qCache (tail : List Bool) (budget : Rat) (number : Nat) : List Bool :=
  RatInput.Encoder.packet (Global.qValue number) (RatInput.Encoder.packet budget tail)

def rCache (tail : List Bool) (budget : Rat) (number : Nat) : List Bool :=
  RatInput.Encoder.packet (Global.rValue number) (qCache tail budget number)

def loopCache (tail : List Bool) (budget : Rat) (number exponent : Nat) : List Bool :=
  RatInput.Encoder.packet (Global.yValue budget exponent) (rCache tail budget number)

variable {background : Bank} {tail : List Bool} {budget : Rat} {number limit B : Nat}

theorem q_width (basis : Basis background tail budget number limit B) : field (Global.qValue number) ≤ 5*B := by
  have rawBound := q_field number
  have n := basis.numberBound
  omega

theorem r_width (basis : Basis background tail budget number limit B) : field (Global.rValue number) ≤ 10*B := by
  have rawBound := r_field number
  have n := basis.numberBound
  omega

theorem n_width (basis : Basis background tail budget number limit B) : field (number : Rat) ≤ 2*B := by
  have rawBound := nat_field number
  have n := basis.numberBound
  omega

theorem twice_n_width (basis : Basis background tail budget number limit B) : field (2*(number : Rat)) ≤ 5*B := by
  have rawBound := twice_nat_field number
  have n := basis.numberBound
  omega

theorem twice_budget_width (basis : Basis background tail budget number limit B) : field (2*budget) ≤ 4*B := by
  have rawBound := QLoop.double_field budget
  change field (2*budget) ≤ field budget+3 at rawBound
  have b := basis.budgetBound
  have one := basis.positive
  omega

theorem y_width (basis : Basis background tail budget number limit B) (exponent : Nat) (within : exponent ≤ limit) :
    field (Global.yValue budget exponent) ≤ 4*B := by
  have rawBound := y_field budget exponent
  have b := basis.budgetBound
  have e := basis.limitBound
  omega

theorem q_cache_length (basis : Basis background tail budget number limit B) :
    (qCache tail budget number).length ≤ 32*B := by
  have q := q_width basis
  have b := basis.budgetBound
  have t := basis.tailBound
  have one := basis.positive
  unfold qCache
  rw [RatInput.Encoder.packet_length,RatInput.Encoder.packet_length]
  change 2*field (Global.qValue number)+6+(2*field budget+6+tail.length) ≤ _
  omega

theorem r_cache_length (basis : Basis background tail budget number limit B) :
    (rCache tail budget number).length ≤ 64*B := by
  have r := r_width basis
  have q := q_cache_length basis
  have one := basis.positive
  unfold rCache
  rw [RatInput.Encoder.packet_length]
  change 2*field (Global.rValue number)+6+(qCache tail budget number).length ≤ _
  omega

theorem q_packet_length (basis : Basis background tail budget number limit B) :
    (RatInput.Encoder.packet (Global.qValue number) []).length ≤ 16*B := by
  have q := q_width basis
  have one := basis.positive
  rw [RatInput.Encoder.packet_length]
  change 2*field (Global.qValue number)+6+0 ≤ _
  omega

theorem loop_cache_length (basis : Basis background tail budget number limit B) (exponent : Nat) (within : exponent ≤ limit) :
    (loopCache tail budget number exponent).length ≤ 128*B := by
  have y := y_width basis exponent within
  have r := r_cache_length basis
  have one := basis.positive
  unfold loopCache
  rw [RatInput.Encoder.packet_length]
  change 2*field (Global.yValue budget exponent)+6+(rCache tail budget number).length ≤ _
  omega

theorem exponent_raw (basis : Basis background tail budget number limit B) (exponent : Nat) (within : exponent ≤ limit) :
    (raw exponent).length ≤ B := by
  have width := raw_length exponent
  have e := basis.limitBound
  omega

theorem exponent_packet (basis : Basis background tail budget number limit B) (exponent : Nat) (within : exponent ≤ limit) :
    (B23_4_RatWordPrep.NatField.packet exponent []).length ≤ 4*B := by
  have width := exponent_raw basis exponent within
  have one := basis.positive
  rw [natural_packet_length]
  simp only [List.length_nil]
  omega

theorem initial_nat_scale (basis : Basis background tail budget number limit B) :
    NatToRat.scale (Global.bank background (qCache tail budget number) [] [] [] [] []) number
      (RatInput.Encoder.packet (Global.qValue number) []) ≤ 1000000*B := by
  have rawBound := natural_scale (Global.bank background (qCache tail budget number) [] [] [] [] []) number
    (RatInput.Encoder.packet (Global.qValue number) [])
  have bank := global_bank_mass background (qCache tail budget number)
  have cache := q_cache_length basis
  have output := q_packet_length basis
  have old := basis.massBound
  have n := basis.numberBound
  omega

theorem first_binary_scale (basis : Basis background tail budget number limit B) :
    binaryScale background (qCache tail budget number) [] 2 (number : Rat)
      (RatInput.Encoder.packet (Global.qValue number) []) ≤ 1024*B := by
  have old := basis.massBound
  have cache := q_cache_length basis
  have output := q_packet_length basis
  have natural := n_width basis
  have one := basis.positive
  unfold binaryScale
  have two : field (2 : Rat)=3 := QLoop.two_field
  rw [two]
  simp only [List.length_nil]
  omega

theorem second_binary_scale (basis : Basis background tail budget number limit B) :
    binaryScale background (qCache tail budget number) [] (2*(number : Rat)) (Global.qValue number) [] ≤ 1024*B := by
  have old := basis.massBound
  have cache := q_cache_length basis
  have q := q_width basis
  have natural := twice_n_width basis
  have one := basis.positive
  unfold binaryScale
  simp only [List.length_nil]
  omega

theorem third_binary_scale (basis : Basis background tail budget number limit B) :
    binaryScale background (rCache tail budget number) [] 2 budget [] ≤ 1024*B := by
  have old := basis.massBound
  have cache := r_cache_length basis
  have b := basis.budgetBound
  have one := basis.positive
  unfold binaryScale
  have two : field (2 : Rat)=3 := QLoop.two_field
  rw [two]
  simp only [List.length_nil]
  omega

theorem compare_binary_scale (basis : Basis background tail budget number limit B) (exponent : Nat) (within : exponent ≤ limit) :
    binaryScale background (loopCache tail budget number exponent) (B23_4_RatWordPrep.NatField.packet exponent [])
      (Global.rValue number) (Global.yValue budget exponent) [] ≤ 1024*B := by
  have old := basis.massBound
  have cache := loop_cache_length basis exponent within
  have packet := exponent_packet basis exponent within
  have r := r_width basis
  have y := y_width basis exponent within
  have one := basis.positive
  unfold binaryScale
  simp only [List.length_nil]
  omega

theorem repeat_binary_scale (basis : Basis background tail budget number limit B) (exponent : Nat) (within : exponent ≤ limit) :
    binaryScale background (loopCache tail budget number exponent) (B23_4_RatWordPrep.NatField.packet exponent [])
      2 (Global.yValue budget exponent) [] ≤ 1024*B := by
  have old := basis.massBound
  have cache := loop_cache_length basis exponent within
  have packet := exponent_packet basis exponent within
  have y := y_width basis exponent within
  have one := basis.positive
  unfold binaryScale
  have two : field (2 : Rat)=3 := QLoop.two_field
  rw [two]
  simp only [List.length_nil]
  omega

end RootB234.ECost
