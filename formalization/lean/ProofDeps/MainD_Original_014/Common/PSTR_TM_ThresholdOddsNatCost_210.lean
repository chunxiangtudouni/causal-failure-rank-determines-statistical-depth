module
public import Common.PSTR_TM_ThresholdOddsNat_209

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdOddsNatCost210
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdOddsNat209

private theorem pred_arithmetic (width first inverse : Nat)
    (hf : first ≤ 32*(width + 1)) (hi : inverse ≤ 32*(width + 1)^2) :
    first + inverse ≤ 128*(width + 1)^2 := by
  nlinarith [Nat.zero_le (width^2)]

theorem rawPred_length_le (archive : List Bool) (value : Nat) (hv : 1 < value) :
    (rawPredTrace archive value).length ≤ 128*(natBits value + 1)^2 := by
  have hp := PSTRTMThresholdPredFrame208.pred_length_le archive value hv
  have hi := PA17TMRatArithmeticUnblock004.framed_time_le archive
    (PSTRTMNatValue017.rawPayload (value - 1)) []
  have hl : (PSTRTMNatValue017.rawPayload (value - 1)).length = natBits (value - 1) := by
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
  rw [hl] at hi
  have hw := PSTRTMArithmetic008.natBits_mono (Nat.sub_le value 1)
  have hs := Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) 2
  have hi' := hi.trans (Nat.mul_le_mul_left 32 hs)
  simp only [rawPredTrace,List.length_append,List.length_map]
  exact pred_arithmetic _ _ _ hp hi'

theorem rawPred_visitedSpace_le (archive : List Bool) (value inputLength : Nat) (hv : 1 < value) :
    visitedSpace rawPredMachine inputLength (rawPredTrace archive value) ≤
      inputLength + 256*(natBits value + 1)^2 + 1 := by
  have ht := rawPred_length_le archive value hv
  have hs := PSTRTMTrace002.visitedSpace_le rawPredMachine inputLength (rawPredTrace archive value)
  omega

private theorem scale_cube (input depth : Nat) : input + 1 ≤ (input + depth + 1)^3 := by
  have hp : 1 ≤ input + depth + 1 := by omega
  have hp2 : input + depth + 1 ≤ (input + depth + 1)^2 := by
    simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (input + depth + 1) hp
  have hp3 : (input + depth + 1)^2 ≤ (input + depth + 1)^3 :=
    Nat.pow_le_pow_right hp (by decide : 2 ≤ 3)
  omega

private theorem arithmetic_time (input depth width main pred : Nat)
    (hm : main ≤ 33554432*(input + depth + 1)^3)
    (hp : pred ≤ 128*(width + 1)^2) (hw : width ≤ input + 7) :
    main + pred ≤ 67108864*(input + depth + 1)^3 := by
  let scale := input + depth + 1
  have hs : 1 ≤ scale := by dsimp only [scale]; omega
  have hwidth : width + 1 ≤ 8*scale := by dsimp only [scale]; omega
  have hw2 := Nat.pow_le_pow_left hwidth 2
  have hp2 : pred ≤ 8192*scale^2 := by nlinarith
  have hp3 : scale^2 ≤ scale^3 := Nat.pow_le_pow_right hs (by decide : 2 ≤ 3)
  have hp4 := hp2.trans (Nat.mul_le_mul_left 8192 hp3)
  change main + pred ≤ 67108864*scale^3
  have hm' : main ≤ 33554432*scale^3 := hm
  omega

theorem oddsNat_length_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    (oddsNatTrace risk depth).length ≤
      67108864*((encode [.rational risk,.natural depth]).length + depth + 1)^3 := by
  have hm := PSTRTMThresholdDenominatorCost201.targetDen_length_le risk depth hr hd
  have hp := rawPred_length_le (PSTRTMThresholdBReblock195.savedLeft risk depth)
    (4*(PaperProofs.Statistics.controllerB risk depth + 1)) (by omega)
  have hw := PSTRTMThresholdDenominatorCost201.targetDen_bits_le risk depth hr hd
  simp only [oddsNatTrace,List.length_append,List.length_map]
  exact arithmetic_time _ _ _ _ _ hm hp hw

theorem oddsNat_visitedSpace_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    visitedSpace oddsNatMachine (encode [.rational risk,.natural depth]).length (oddsNatTrace risk depth) ≤
      268435456*((encode [.rational risk,.natural depth]).length + depth + 1)^3 := by
  have ht := oddsNat_length_le risk depth hr hd
  have hs := PSTRTMTrace002.visitedSpace_le oddsNatMachine
    (encode [.rational risk,.natural depth]).length (oddsNatTrace risk depth)
  have hp := scale_cube (encode [.rational risk,.natural depth]).length depth
  omega

/-- Original input, exact canonical raw odds integer, SAME real Runs and
visitedSpace, true HALT. This is neither rational Datum serialization nor
the full five-output threshold machine. -/
theorem original_oddsNat_computes (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    computes oddsNatMachine (encode [.rational risk,.natural depth])
      (encodeNat (4*(PaperProofs.Statistics.controllerB risk depth + 1) - 1))
      (268435456*((encode [.rational risk,.natural depth]).length + depth + 1)^3)
      (268435456*((encode [.rational risk,.natural depth]).length + depth + 1)^3) := by
  refine ⟨oddsNatTrace risk depth,oddsNatFinal risk depth,oddsNat_runs risk depth hr hd,?_,?_,
    oddsNat_visitedSpace_le risk depth hr hd⟩
  · rw [oddsNat_final_tape]
    simp only [Turing.Tape.mk₂,Turing.Tape.mk'_right₀]
  · have ht := oddsNat_length_le risk depth hr hd
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdOddsNatCost210
