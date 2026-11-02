module
public import Common.PSTR_TM_ThresholdBReblock_195

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBReblockCost196
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBReblock195

private theorem scale_cube (input depth : Nat) : input + 1 ≤ (input + depth + 1)^3 := by
  have hp : 1 ≤ input + depth + 1 := by omega
  have hp2 : input + depth + 1 ≤ (input + depth + 1)^2 := by
    simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (input + depth + 1) hp
  have hp3 : (input + depth + 1)^2 ≤ (input + depth + 1)^3 :=
    Nat.pow_le_pow_right hp (by decide : 2 ≤ 3)
  omega

private theorem arithmetic_time (input depth width main reblock : Nat)
    (hm : main ≤ 8388608*(input + depth + 1)^3)
    (hr : reblock ≤ 32*(width + 1)^2) (hw : width ≤ input + 4) :
    main + reblock ≤ 16777216*(input + depth + 1)^3 := by
  let scale := input + depth + 1
  have hp : 1 ≤ scale := by dsimp only [scale]; omega
  have hwidth : width + 1 ≤ 5*scale := by dsimp only [scale]; omega
  have hw2 := Nat.pow_le_pow_left hwidth 2
  have hr2 : reblock ≤ 800*scale^2 := by nlinarith
  have hp3 : scale^2 ≤ scale^3 := Nat.pow_le_pow_right hp (by decide : 2 ≤ 3)
  have hr3 := hr2.trans (Nat.mul_le_mul_left 800 hp3)
  change main + reblock ≤ 16777216*scale^3
  have hm' : main ≤ 8388608*scale^3 := hm
  omega

private theorem reblock_polynomial (width : Nat) :
    width^2 + 11*width + 12 ≤ 32*(width + 1)^2 := by
  nlinarith [Nat.zero_le (width^2)]

theorem saved_length_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    (savedTrace risk depth).length ≤
      16777216*((encode [.rational risk,.natural depth]).length + depth + 1)^3 := by
  have hm := PSTRTMThresholdBBackupBound193.backup_length_le risk depth hr hd
  have hc := reblock_length (savedLeft risk depth)
    (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))
  have hl : (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)).length =
      natBits (PaperProofs.Statistics.controllerB risk depth) := by
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
  rw [hl] at hc
  have hc' := hc.le.trans (reblock_polynomial _)
  have hw := PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
  simp only [savedTrace,List.length_append,List.length_map]
  exact arithmetic_time _ _ _ _ _ hm hc' hw

theorem saved_visitedSpace_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    visitedSpace savedMachine (encode [.rational risk,.natural depth]).length (savedTrace risk depth) ≤
      67108864*((encode [.rational risk,.natural depth]).length + depth + 1)^3 := by
  have ht := saved_length_le risk depth hr hd
  have hs := PSTRTMTrace002.visitedSpace_le savedMachine
    (encode [.rational risk,.natural depth]).length (savedTrace risk depth)
  have hp := scale_cube (encode [.rational risk,.natural depth]).length depth
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBReblockCost196
