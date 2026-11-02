module

public import Common.PSTR_SYM_HeaderErase_019
public import Common.PSTR_SYM_ZeroOutput_014

/-! Actual original N0 input to a retained flagged q+2 count and a truly
cleared data strip, with the head on the original EOF TRUE. This producer
does not yet emit symbolicOutput. N0/positive selection still needs one
fixed real input branch; no host-dependent machine selection is claimed. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicZeroErase

open PaperProofs.Common Turing
open PSTRSymbolicLocator (naturalPrefix outerLeft rawInstance_zero)
open PSTRSymbolicHeaderErase

def zeroNumbers {q : Nat} (available : Finset (Fin q)) : List Nat :=
  [0, q] ++ (List.finRange q).map (fun tool => if decide (tool ∈ available) then 1 else 0)

theorem zeroNumbers_length {q : Nat} (available : Finset (Fin q)) :
    (zeroNumbers available).length = q + 2 := by
  simp only [zeroNumbers, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_finRange]
  omega

theorem zero_data {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool)
    (zero : I.stageCount = 0) :
    rawInstance input ++ rawSet available = (zeroNumbers available).map Datum.natural := by
  rw [rawInstance_zero input zero]
  simp only [zeroNumbers, List.map_append, List.map_cons, List.map_nil]
  congr 1
  simp only [rawSet, List.map_map, Function.comp_def, boolDatum]

theorem zero_input_bits {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool)
    (zero : I.stageCount = 0) :
    CompactPrice.symbolicInput input available =
      encodeNat (I.toolCount + 2) ++ (naturalPrefix (zeroNumbers available) ++ [true]) := by
  unfold CompactPrice.symbolicInput
  rw [zero_data input available zero]
  simp only [encode, List.length_map, zeroNumbers_length, List.flatMap_map,
    naturalPrefix, List.append_assoc]

/-- ONE fixed47-label machine before all original instances and tools.
The SAME trace proves original Runs/eval, entire Tape, time and original
visitedSpace charged on the FULL original symbolicInput length. -/
theorem original_zero_erase {I : Instance} (input : StatisticalInput I)
    (available : Finset I.Tool) (zero : I.stageCount = 0) :
    ∃ (trace : List (MachineState 46)) (final : MachineState 46),
      Runs headerEraseMachine (CompactPrice.symbolicInput input available) trace final ∧
      final.Tape = Tape.mk₂
        (List.replicate (naturalPrefix (zeroNumbers available)).length false ++
          outerLeft [] (I.toolCount + 2)) [true] ∧
      trace.length ≤ 256 * ((CompactPrice.symbolicInput input available).length + 1)^2 ∧
      visitedSpace headerEraseMachine (CompactPrice.symbolicInput input available).length trace ≤
        256 * ((CompactPrice.symbolicInput input available).length + 1)^2 := by
  let numbers := zeroNumbers available
  let count := I.toolCount + 2
  let trace := headerEraseTrace [] count numbers []
  let final := headerEraseFinal [] count numbers []
  have bits := zero_input_bits input available zero
  have segment := headerErase_runsFrom [] count numbers []
  have actual : Runs headerEraseMachine (CompactPrice.symbolicInput input available) trace final := by
    apply PSTRTMTrace002.runs_of_chain
    · have first := segment.1
      rw [← bits] at first
      simpa only [trace, count, numbers, TM0.init, Tape.mk₁, Fin.default_eq_zero] using first
    · exact segment.2.1
    · exact segment.2.2.1
    · exact segment.2.2.2
  have room : (encodeNat count).length + (naturalPrefix numbers).length + 1 ≤
      (CompactPrice.symbolicInput input available).length + 1 := by
    rw [bits]
    simp only [List.length_append, List.length_cons, List.length_nil]
    change (encodeNat count).length + (naturalPrefix numbers).length + 1 ≤
      (encodeNat count).length + ((naturalPrefix numbers).length + 1) + 1
    omega
  have square := Nat.pow_le_pow_left room 2
  have time := headerErase_time_le [] count numbers []
  have timeUpper := Nat.mul_le_mul_left 64 square
  have cells := headerErase_space_le (CompactPrice.symbolicInput input available).length [] count numbers []
  have spaceUpper := Nat.mul_le_mul_left 128 square
  have inputRoom : (CompactPrice.symbolicInput input available).length + 1 ≤
      ((CompactPrice.symbolicInput input available).length + 1)^2 := by nlinarith
  refine ⟨trace, final, actual, ?_, ?_, ?_⟩
  · exact headerErase_final_tape [] count numbers []
  · change (headerEraseTrace [] count numbers []).length ≤ _
    omega
  · change visitedSpace headerEraseMachine (CompactPrice.symbolicInput input available).length
      (headerEraseTrace [] count numbers []) ≤ _
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicZeroErase
