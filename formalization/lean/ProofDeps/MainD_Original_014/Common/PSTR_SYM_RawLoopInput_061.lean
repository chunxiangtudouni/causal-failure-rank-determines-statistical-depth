module

public import Common.PSTR_SYM_RawLoopCycle_060

/-! SOURCEONLY. Original positive-N data supplies the internal room and
positivity obligations of the real cursor loop. No new original caller
qualification, supplied archive/count/width, or runtime answer is added. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop

open PaperProofs.Common Turing PSTRTMSeq005 PSTRTMIncrement009 PSTRTMRawNat010
open PSTRTMThresholdCountdownCode164 PSTRSymbolicCounter PSTRSymbolicRawBootstrap
open PSTRSymbolicPairedArchive PSTRSymbolicLaneScan PSTRSymbolicLaneArchive PSTRSymbolicCursorArchive

theorem original_positive_remaining {I : Instance} (input : StatisticalInput I)
    (available : Finset I.Tool) (positive : 0 < I.stageCount) :
    3 ≤ (originalRemaining input available).length := by
  have stagesNonempty : List.finRange I.stageCount ≠ [] := by
    intro empty
    have length := congrArg List.length empty
    simp only [List.length_finRange,List.length_nil] at length
    omega
  obtain ⟨stage,later,stages⟩ := List.exists_cons_of_ne_nil stagesNonempty
  change 3 ≤ (I.compatibility.flatMap rawSet ++
    (List.finRange I.stageCount).flatMap (fun point => rawExperiment (input.experiment point)) ++
    (List.finRange I.stageCount).flatMap (fun point => (List.finRange I.toolCount).map
      (fun tool => Datum.rational (input.correctionFee point tool))) ++ rawSet available).length
  erw [stages,List.flatMap_cons]
  have experimentRoom : 3 ≤ (rawExperiment (input.experiment stage)).length := by
    simp only [rawExperiment,List.length_append,List.length_cons,List.length_nil]
    omega
  simp only [List.length_append]
  omega

theorem original_positive_header {I : Instance} (input : StatisticalInput I)
    (available : Finset I.Tool) (positive : 0 < I.stageCount) :
    3 ≤ (afterTwo (rawInstance input ++ rawSet available).length).length ∧
      true ∈ afterTwo (rawInstance input ++ rawSet available).length := by
  let count := (rawInstance input ++ rawSet available).length
  have remaining := original_positive_remaining input available positive
  have fields : rawInstance input ++ rawSet available =
      .natural I.stageCount :: .natural I.toolCount :: originalRemaining input available := rfl
  have countLength := congrArg List.length fields
  simp only [List.length_cons] at countLength
  have countRoom : 4 ≤ count := by change 4 ≤ (rawInstance input ++ rawSet available).length; omega
  have width := (two_count_rounds count (by omega)).2.2.2
  have logRoom : natBits 4 ≤ natBits count := by
    simp only [natBits,Nat.log2_eq_log_two]
    exact Nat.add_le_add_right (Nat.log_mono_right countRoom) 1
  have four : natBits 4 = 3 := by decide
  rw [four] at logRoom
  refine ⟨?_,?_⟩
  · change 3 ≤ (afterTwo count).length
    rw [width,PSTRSymbolicLocator.rawPayload_length]
    exact logRoom
  · apply has_true_of_value_pos
    rw [original_remaining_count]
    omega

theorem bootstrap_archive (count stage tools : Nat) (suffix : List Bool) (tag : Bool) :
    bootstrapTape count stage tools (tag :: suffix) =
      archiveTape [.natural stage,.natural tools] [] (afterTwo count) suffix tag := by
  simp only [bootstrapTape,archiveTape,allDatumPairs_cells,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.reverse_append,List.append_assoc]

theorem raw_suffix_nonempty (remaining : List Datum) : remaining.flatMap encodeDatum ++ [true] ≠ [] := by
  simp

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop
