module

public import Common.PSTR_SYM_OriginalFront_029
public import Common.PSTR_TM_ThresholdDepthZeroRun_168

/-! Actual original outer-count producer for the heterogeneous raw scanner.
The real first Natural tag supplies END00. The arbitrary-width binary count
is retained in actual flagged cells, not in an original structural Word.
This produces no complete field loop, EOF detector, AST or serializer. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCounter

open PaperProofs.Common Turing PSTRTMSeq005 PA17TMRatArithmeticParse002
open PSTRSymbolicLocator (outerLeft rawPayload_length)

def counterEntryMachine : Machine 23 := seqMachine streamMachine fieldBackMachine

def counterEntryTrace (count : Nat) (suffix : List Bool) : List (MachineState 23) :=
  (streamTrace [] [] (PSTRTMNatValue017.rawPayload count) (false :: suffix)).map (leftCfg (b := 5)) ++
    (fieldBackTrace [] (PSTRTMNatValue017.rawPayload count) (false :: suffix)).map (rightCfg (a := 17))

def counterEntryFinal (count : Nat) (suffix : List Bool) : MachineState 23 :=
  rightCfg (a := 17) (fieldBackFinal [] (PSTRTMNatValue017.rawPayload count) (false :: suffix))

theorem counterEntry_runsFrom (count : Nat) (suffix : List Bool) :
    RunsFrom counterEntryMachine ⟨0, Tape.mk₁ (encodeNat count ++ false :: suffix)⟩
      (counterEntryTrace count suffix) (counterEntryFinal count suffix) := by
  apply seq_runsFrom streamMachine fieldBackMachine
    ⟨0, Tape.mk₁ (encodeNat count ++ false :: suffix)⟩
    (streamFinal [] (PSTRTMNatValue017.rawPayload count) (false :: suffix))
    (fieldBackFinal [] (PSTRTMNatValue017.rawPayload count) (false :: suffix))
    (streamTrace [] [] (PSTRTMNatValue017.rawPayload count) (false :: suffix))
    (fieldBackTrace [] (PSTRTMNatValue017.rawPayload count) (false :: suffix))
  · exact encodeNat_stream_runsFrom [] (false :: suffix) count
  · change RunsFrom fieldBackMachine ⟨0, Tape.mk₂ (outerLeft [] count) (false :: suffix)⟩ _ _
    rw [PSTRSymbolicZeroTail.outer_guard]
    exact fieldBack_runsFrom [] (PSTRTMNatValue017.rawPayload count) (false :: suffix)

theorem counterEntry_final_tape (count : Nat) (suffix : List Bool) :
    (counterEntryFinal count suffix).Tape = Tape.mk₂ [false]
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload count) ++ false :: false :: suffix) :=
  fieldBack_final_tape [] (PSTRTMNatValue017.rawPayload count) (false :: suffix)

theorem counterEntry_time_le (count : Nat) (suffix : List Bool) :
    (counterEntryTrace count suffix).length ≤ 32 * (natBits count + 1)^2 := by
  have header := stream_length_le [] (PSTRTMNatValue017.rawPayload count) (false :: suffix)
  rw [rawPayload_length] at header
  simp only [counterEntryTrace, List.length_append, List.length_map, fieldBackTrace_length,
    rawPayload_length]
  nlinarith [Nat.zero_le ((natBits count)^2)]

theorem original_data_count_pos {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) :
    2 ≤ (rawInstance input ++ rawSet available).length := by
  unfold rawInstance
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- The original input itself supplies the count, its actual flag cells,
the leading guard and both real END00 cells. All suffix cells are retained.
There is no computed count/width/window/trace field in the original input. -/
theorem original_counter_entry {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) :
    ∃ (trace : List (MachineState 23)) (final : MachineState 23),
      Runs counterEntryMachine (CompactPrice.symbolicInput input available) trace final ∧
      final.Tape = Tape.mk₂ [false]
        (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (rawInstance input ++ rawSet available).length) ++
          false :: false :: (encodeNat I.stageCount ++
            ((PSTRSymbolicFront.originalRemainder input available).flatMap encodeDatum ++ [true]))) ∧
      2 ≤ (rawInstance input ++ rawSet available).length ∧
      trace.length ≤ 64 * ((CompactPrice.symbolicInput input available).length + 1)^2 ∧
      ∀ clock, visitedSpace counterEntryMachine (CompactPrice.symbolicInput input available).length
        (trace.take clock) ≤ 256 * ((CompactPrice.symbolicInput input available).length + 1)^2 := by
  let count := (rawInstance input ++ rawSet available).length
  let suffix := encodeNat I.stageCount ++
    ((PSTRSymbolicFront.originalRemainder input available).flatMap encodeDatum ++ [true])
  have bits : CompactPrice.symbolicInput input available = encodeNat count ++ false :: suffix := by
    simpa only [count, suffix, encodeDatum, List.cons_append, List.append_assoc] using
      PSTRSymbolicFront.original_front_bits input available
  let trace := counterEntryTrace count suffix
  let final := counterEntryFinal count suffix
  have segment := counterEntry_runsFrom count suffix
  rw [← bits] at segment
  have actual := PSTRSymbolicFront.original_front_runs counterEntryMachine _ trace final segment
  have time := counterEntry_time_le count suffix
  have width := PSTRSymbolicFront.original_count_room input available
  change natBits count + 1 ≤ (CompactPrice.symbolicInput input available).length + 1 at width
  have square := Nat.pow_le_pow_left width 2
  have scaled := Nat.mul_le_mul_left 32 square
  have total : trace.length ≤ 64 * ((CompactPrice.symbolicInput input available).length + 1)^2 := by
    change (counterEntryTrace count suffix).length ≤ _
    omega
  have inputRoom : (CompactPrice.symbolicInput input available).length + 1 ≤
      ((CompactPrice.symbolicInput input available).length + 1)^2 := by nlinarith
  refine ⟨trace, final, actual, counterEntry_final_tape count suffix,
    original_data_count_pos input available, total, ?_⟩
  intro clock
  have cells := PSTRTMTrace002.visitedSpace_le counterEntryMachine
    (CompactPrice.symbolicInput input available).length (trace.take clock)
  have takeLength : (trace.take clock).length ≤ trace.length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCounter
