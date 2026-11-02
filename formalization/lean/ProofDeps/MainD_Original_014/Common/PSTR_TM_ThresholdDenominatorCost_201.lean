module
public import Common.PSTR_TM_ThresholdDenominator_200

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDenominatorCost201
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDenominator200

private theorem scale_cube (input depth : Nat) : input + 1 ≤ (input + depth + 1)^3 := by
  have hp : 1 ≤ input + depth + 1 := by omega
  have hp2 : input + depth + 1 ≤ (input + depth + 1)^2 := by
    simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (input + depth + 1) hp
  have hp3 : (input + depth + 1)^2 ≤ (input + depth + 1)^3 :=
    Nat.pow_le_pow_right hp (by decide : 2 ≤ 3)
  omega

theorem targetDen_length_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    (targetDenTrace risk depth).length ≤
      33554432*((encode [.rational risk,.natural depth]).length + depth + 1)^3 := by
  have hm := PSTRTMThresholdBReblockCost196.saved_length_le risk depth hr hd
  have ha := PSTRTMThresholdDenominatorFrame199.denominator_length_le
    (PSTRTMThresholdBReblock195.savedLeft risk depth) (PaperProofs.Statistics.controllerB risk depth)
  have hw := PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
  have hp := scale_cube (encode [.rational risk,.natural depth]).length depth
  simp only [targetDenTrace,List.length_append,List.length_map]
  omega

theorem targetDen_visitedSpace_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    visitedSpace targetDenMachine (encode [.rational risk,.natural depth]).length (targetDenTrace risk depth) ≤
      134217728*((encode [.rational risk,.natural depth]).length + depth + 1)^3 := by
  have ht := targetDen_length_le risk depth hr hd
  have hs := PSTRTMTrace002.visitedSpace_le targetDenMachine
    (encode [.rational risk,.natural depth]).length (targetDenTrace risk depth)
  have hp := scale_cube (encode [.rational risk,.natural depth]).length depth
  omega

theorem targetDen_bits_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    natBits (4*(PaperProofs.Statistics.controllerB risk depth + 1)) ≤
      (encode [.rational risk,.natural depth]).length + 7 := by
  have hb := PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
  have h1 := PSTRTMArithmetic008.natBits_add_le (PaperProofs.Statistics.controllerB risk depth) 1
  have ho : natBits 1 = 1 := by decide
  rw [ho] at h1
  have h2 := PSTRTMThresholdDenominatorFrame199.double_width
    (PaperProofs.Statistics.controllerB risk depth + 1) (by omega)
  have h3 := PSTRTMThresholdDenominatorFrame199.double_width
    (2*(PaperProofs.Statistics.controllerB risk depth + 1)) (by omega)
  have he : 2*(2*(PaperProofs.Statistics.controllerB risk depth + 1)) =
      4*(PaperProofs.Statistics.controllerB risk depth + 1) := by omega
  rw [he] at h3
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDenominatorCost201
