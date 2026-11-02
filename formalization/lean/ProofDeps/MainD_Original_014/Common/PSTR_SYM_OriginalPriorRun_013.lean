module

public import Common.PSTR_SYM_OriginalPriorData_012

/-! A real fixed83-label staging producer from ORIGINAL symbolicInput,
in its positive-N branch. This returns parsed prior fields and the ENTIRE
original remaining suffix, not symbolicOutput or an allocated arithmetic port. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLocator

open PaperProofs.Common Turing PA17TMRatArithmeticParse002

theorem original_positive_prior {I : Instance} (input : StatisticalInput I)
    (available : Finset I.Tool) (positive : 0 < I.stageCount) :
    ∃ (numbers : List Nat) (remaining : List Datum)
      (trace : List (MachineState 82)) (final : MachineState 82),
      rawInstance input ++ rawSet available = numbers.map Datum.natural ++
        .rational (input.experiment (firstStage positive)).priorOne :: remaining ∧
      Runs firstRatMachine (CompactPrice.symbolicInput input available) trace final ∧
      final.Tape = Tape.mk₂
        (ratLeft (firstRatArchive [] (rawInstance input ++ rawSet available).length numbers)
          (input.experiment (firstStage positive)).priorOne)
        (remaining.flatMap encodeDatum ++ [true]) ∧
      trace.length ≤ 256 * ((CompactPrice.symbolicInput input available).length + 1)^2 ∧
      visitedSpace firstRatMachine (CompactPrice.symbolicInput input available).length trace ≤
        256 * ((CompactPrice.symbolicInput input available).length + 1)^2 := by
  obtain ⟨numbers, remaining, data, bits⟩ := original_prior_bits input available positive
  let count := (rawInstance input ++ rawSet available).length
  let value := (input.experiment (firstStage positive)).priorOne
  let suffix := remaining.flatMap encodeDatum ++ [true]
  let trace := firstRatTrace [] count numbers value suffix
  let final := firstRatFinal [] count numbers value suffix
  have segment := firstRat_runsFrom [] count numbers value suffix
  have actual : Runs firstRatMachine (CompactPrice.symbolicInput input available) trace final := by
    apply PSTRTMTrace002.runs_of_chain
    · have first := segment.1
      rw [← bits] at first
      simpa only [trace, count, value, suffix, TM0.init, Tape.mk₁, Fin.default_eq_zero] using first
    · exact segment.2.1
    · exact segment.2.2.1
    · exact segment.2.2.2
  have room : (encodeNat count).length + (naturalPrefix numbers).length +
      (encodeDatum (.rational value)).length + 1 ≤ (CompactPrice.symbolicInput input available).length + 1 := by
    rw [bits]
    change (encodeNat count).length + (naturalPrefix numbers).length +
      (encodeDatum (.rational value)).length + 1 ≤
      (encodeNat count ++ (naturalPrefix numbers ++ encodeDatum (.rational value) ++ suffix)).length + 1
    simp only [List.length_append]
    omega
  have square := Nat.pow_le_pow_left room 2
  have clock := firstRat_time_le [] count numbers value suffix
  have timeUpper := Nat.mul_le_mul_left 64 square
  have cells := firstRat_space_le (CompactPrice.symbolicInput input available).length [] count numbers value suffix
  have spaceUpper := Nat.mul_le_mul_left 128 square
  have inputRoom : (CompactPrice.symbolicInput input available).length + 1 ≤
      ((CompactPrice.symbolicInput input available).length + 1)^2 := by nlinarith
  refine ⟨numbers,remaining,trace,final,data,actual,?_,?_,?_⟩
  · exact firstRat_final_tape [] count numbers value suffix
  · change (firstRatTrace [] count numbers value suffix).length ≤ _
    omega
  · change visitedSpace firstRatMachine (CompactPrice.symbolicInput input available).length
      (firstRatTrace [] count numbers value suffix) ≤ _
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLocator
