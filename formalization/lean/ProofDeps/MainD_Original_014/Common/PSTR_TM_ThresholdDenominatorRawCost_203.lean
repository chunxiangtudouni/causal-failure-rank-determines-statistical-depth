module
public import Common.PSTR_TM_ThresholdDenominatorRaw_202

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDenominatorRawCost203
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDenominatorRaw202

private theorem scale_cube (input depth : Nat) : input + 1 ≤ (input + depth + 1)^3 := by
  have hp : 1 ≤ input + depth + 1 := by omega
  have hp2 : input + depth + 1 ≤ (input + depth + 1)^2 := by
    simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (input + depth + 1) hp
  have hp3 : (input + depth + 1)^2 ≤ (input + depth + 1)^3 :=
    Nat.pow_le_pow_right hp (by decide : 2 ≤ 3)
  omega

private theorem arithmetic_time (input depth width main inverse : Nat)
    (hm : main ≤ 33554432*(input + depth + 1)^3)
    (hi : inverse ≤ 32*(width + 1)^2) (hw : width ≤ input + 7) :
    main + inverse ≤ 67108864*(input + depth + 1)^3 := by
  let scale := input + depth + 1
  have hp : 1 ≤ scale := by dsimp only [scale]; omega
  have hwidth : width + 1 ≤ 8*scale := by dsimp only [scale]; omega
  have hw2 := Nat.pow_le_pow_left hwidth 2
  have hi2 : inverse ≤ 2048*scale^2 := by nlinarith
  have hp3 : scale^2 ≤ scale^3 := Nat.pow_le_pow_right hp (by decide : 2 ≤ 3)
  have hi3 := hi2.trans (Nat.mul_le_mul_left 2048 hp3)
  change main + inverse ≤ 67108864*scale^3
  have hm' : main ≤ 33554432*scale^3 := hm
  omega

theorem rawDen_length_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    (rawDenTrace risk depth).length ≤
      67108864*((encode [.rational risk,.natural depth]).length + depth + 1)^3 := by
  have hm := PSTRTMThresholdDenominatorCost201.targetDen_length_le risk depth hr hd
  have hi := PA17TMRatArithmeticUnblock004.framed_time_le
    (PSTRTMThresholdBReblock195.savedLeft risk depth)
    (PSTRTMNatValue017.rawPayload (4*(PaperProofs.Statistics.controllerB risk depth + 1))) []
  have hl : (PSTRTMNatValue017.rawPayload (4*(PaperProofs.Statistics.controllerB risk depth + 1))).length =
      natBits (4*(PaperProofs.Statistics.controllerB risk depth + 1)) := by
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
  rw [hl] at hi
  have hw := PSTRTMThresholdDenominatorCost201.targetDen_bits_le risk depth hr hd
  simp only [rawDenTrace,List.length_append,List.length_map]
  exact arithmetic_time _ _ _ _ _ hm hi hw

theorem rawDen_visitedSpace_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    visitedSpace rawDenMachine (encode [.rational risk,.natural depth]).length (rawDenTrace risk depth) ≤
      268435456*((encode [.rational risk,.natural depth]).length + depth + 1)^3 := by
  have ht := rawDen_length_le risk depth hr hd
  have hs := PSTRTMTrace002.visitedSpace_le rawDenMachine
    (encode [.rational risk,.natural depth]).length (rawDenTrace risk depth)
  have hp := scale_cube (encode [.rational risk,.natural depth]).length depth
  omega

theorem original_targetDen_computes (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    computes rawDenMachine (encode [.rational risk,.natural depth])
      (encodeNat (4*(PaperProofs.Statistics.controllerB risk depth + 1)))
      (268435456*((encode [.rational risk,.natural depth]).length + depth + 1)^3)
      (268435456*((encode [.rational risk,.natural depth]).length + depth + 1)^3) := by
  refine ⟨rawDenTrace risk depth,rawDenFinal risk depth,rawDen_runs risk depth hr hd,?_,?_,
    rawDen_visitedSpace_le risk depth hr hd⟩
  · rw [rawDen_final_tape]
    simp only [Turing.Tape.mk₂,Turing.Tape.mk'_right₀]
  · have ht := rawDen_length_le risk depth hr hd
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDenominatorRawCost203
