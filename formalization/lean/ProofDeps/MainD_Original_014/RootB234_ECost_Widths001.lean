module

public import RootB234_PrepExponent_GlobalRun040

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.ECost

open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootB234.PrepExponent

abbrev Stack := RatInput.Stack
abbrev Bank := Stack → List Bool
abbrev field := RatInput.Encoder.fieldSize
abbrev raw := PSTRTMNatValue017.rawPayload

theorem raw_length (number : Nat) : (raw number).length ≤ number+1 := by
  have bound := Nat.log2_le_self number
  simpa only [raw,PSTRTMNatValue017.rawPayload,List.length_ofFn,natBits] using Nat.add_le_add_right bound 1

theorem natural_packet_length (number : Nat) (tail : List Bool) :
    (B23_4_RatWordPrep.NatField.packet number tail).length=2*(raw number).length+2+tail.length := by
  simp only [B23_4_RatWordPrep.NatField.packet,List.length_append,List.length_cons,
    PSTRSymbolicRatExport.flagged_length,raw]
  omega

theorem nat_field_exact (number : Nat) : field (number : Rat)=(raw number).length+1 := by
  have length := congrArg List.length (NatToRat.integer_packet number [])
  rw [RatInput.Encoder.packet_length] at length
  simp only [List.length_cons,List.length_append,List.length_nil,Nat.add_zero] at length
  rw [natural_packet_length] at length
  simp only [List.length_nil,Nat.add_zero] at length
  change RatInput.Encoder.fieldSize (number : Rat)=(raw number).length+1
  omega

theorem nat_field (number : Nat) : field (number : Rat) ≤ number+2 := by
  rw [nat_field_exact]
  have bound := raw_length number
  omega

theorem mul_field (x y : Rat) : field (x*y) ≤ field x+field y := by
  simpa only [field,RootB23.WordOddsBits.ratInput_fieldSize_eq] using RootB23.WordOddsBits.mul_width_le x y

theorem sub_field (x y : Rat) : field (x-y) ≤ 2*(field x+field y) := by
  obtain ⟨numerator,denominator⟩ := PA17TMRatArithmeticNativeSize007.sub_normalized_bits_le x y
  simp only [field,RootB23.WordOddsBits.ratInput_fieldSize_eq,RootB23.WordOddsBits.width]
  dsimp only [PA17TMRatArithmeticNativeSize007.inputBits] at numerator denominator
  omega

theorem q_field (number : Nat) : field (Global.qValue number) ≤ 5+3*number := by
  simpa only [Global.qValue,QLoop.twelve_field] using QLoop.power_field (12 : Rat) number

theorem twice_nat_field (number : Nat) : field (2*(number : Rat)) ≤ number+5 := by
  have multiply := mul_field 2 (number : Rat)
  have natural := nat_field number
  have two : field (2 : Rat)=3 := QLoop.two_field
  omega

theorem r_field (number : Nat) : field (Global.rValue number) ≤ 4*number+10 := by
  have multiply := mul_field (2*(number : Rat)) (Global.qValue number)
  have natural := twice_nat_field number
  have q := q_field number
  change field ((2*(number : Rat))*Global.qValue number) ≤ _
  omega

theorem y_field (budget : Rat) (exponent : Nat) :
    field (Global.yValue budget exponent) ≤ field budget+3*exponent := by
  have bound := QLoop.power_field budget exponent
  have same : budget*(2 : Rat)^exponent=Global.yValue budget exponent := by
    unfold Global.yValue
    ring
  rw [same] at bound
  exact bound

end RootB234.ECost
