module
public import Structure.RootB23_Threshold_OutputArithmetic_OddsFields_006
public import Structure.RootB23_Threshold_OutputArithmetic_BareRats_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.OutputArithmetic.OddsInverse
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002
open RootB23.Threshold.Window

def output (d : Nat) : List Bool := encodeDatum (.rational ((d-1 : Nat) : Rat)) ++
  encodeDatum (.rational (1 / ((d-1 : Nat) : Rat))) ++ [true]

def code : Machine 1014 := PSTRTMSeq005.seqMachine OddsFields.code BareRats.code

theorem inv_num (n : Nat) (positive : 0<n) : (1/(n : Rat)).num = 1 := by
  rw [one_div]
  exact Rat.inv_natCast_num_of_pos positive

theorem inv_den (n : Nat) (positive : 0<n) : (1/(n : Rat)).den = n := by
  rw [one_div]
  exact Rat.inv_natCast_den_of_pos positive

theorem field_word (n : Nat) (positive : 0<n) :
    MarshalSerialize.inputRight (n : Rat) (1/(n : Rat)) [] = OddsFields.right n ++ [false,false] := by
  have unit : PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload 1) = [true,true] := by decide
  simp only [MarshalSerialize.inputRight,numeratorDigits,denominatorDigits,
    Rat.num_natCast,Int.natAbs_natCast,Rat.den_natCast,inv_num n positive,inv_den n positive]
  change PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n) ++
    Uncapped.Serialize.marker (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload 1) ++
      Uncapped.Serialize.marker (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload 1) ++
        Uncapped.Serialize.marker (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n) ++ [false,false]))) = _
  rw [unit]
  simp only [OddsFields.right,OddsFields.gap,Uncapped.Serialize.marker,
    List.append_assoc,List.cons_append,List.nil_append]

theorem width (n : Nat) (positive : 0<n) :
    MarshalSerialize.totalWidth (n : Rat) (1/(n : Rat)) + 1 = 2 * natBits n + 3 := by
  have unit : natBits 1 = 1 := by decide
  simp only [MarshalSerialize.totalWidth,Rat.num_natCast,Int.natAbs_natCast,Rat.den_natCast,
    inv_num n positive,inv_den n positive]
  change natBits n + natBits 1 + natBits 1 + natBits n + 1 = _
  rw [unit]
  omega

private theorem fee (bits total : Nat) (small : total ≤ 5 * (bits+1)) :
    1024*(bits+1)^2 + 1024*total^2 ≤ 32768*(bits+1)^2 := by
  have square := Nat.pow_le_pow_left small 2
  nlinarith only [square,Nat.zero_le ((bits+1)^2)]

/-- Actual D DATA -> two simultaneous canonical rational Datums, followed
by a genuinely written outer TRUE footer. The original FALSE guard and
every external archive cell remain. No N value, room, header or run is an
input, and the fixed code covers every D>=2 including the N=1 case. -/
theorem bounded (archive : List Bool) (d : Nat) (positive : 2≤d) :
    BoundedRun code
      (Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload d))) 1014
      (Tape.mk₂ (false :: archive) (output d)) (32768*(natBits d+1)^2) := by
  have nPositive : 0<d-1 := by omega
  have prepared := OddsFields.bounded archive d positive
  have encoded := BareRats.bounded (false :: archive) ((d-1 : Nat) : Rat) (1/((d-1 : Nat) : Rat))
    (Nat.cast_nonneg _) (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  rw [field_word (d-1) nPositive,Target.two_right_blanks] at encoded
  have actual := prepared.seq encoded
  have port : PSTRTMSeq005.rightLabel (a := 609) (404 : Fin 405) = (1014 : Fin 1015) := by decide
  rw [port] at actual
  have smallBits := PSTRTMArithmetic008.natBits_mono (Nat.sub_le d 1)
  have small : MarshalSerialize.totalWidth ((d-1 : Nat) : Rat) (1/((d-1 : Nat) : Rat)) + 1 ≤
      5*(natBits d+1) := by rw [width (d-1) nPositive];omega
  exact actual.mono (fee (natBits d) _ small)

theorem actual_contract (archive : List Bool) (d : Nat) (positive : 2≤d) :
    ∃ trace, PSTRTMSeq005.RunsFrom code
      ⟨0,Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload d))⟩ trace
      ⟨1014,Tape.mk₂ (false :: archive) (output d)⟩ ∧
      trace.length ≤ 32768*(natBits d+1)^2 ∧
      ∀ chargedLength clock, visitedSpace code chargedLength (trace.take clock) ≤
        chargedLength+65536*(natBits d+1)^2+1 := by
  obtain ⟨trace,run,time⟩ := bounded archive d positive
  refine ⟨trace,run,time,?_⟩
  intro chargedLength clock
  have space := PSTRTMTrace002.visitedSpace_le code chargedLength (trace.take clock)
  have taken : (trace.take clock).length ≤ trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
  omega

end RootB23.Threshold.OutputArithmetic.OddsInverse
