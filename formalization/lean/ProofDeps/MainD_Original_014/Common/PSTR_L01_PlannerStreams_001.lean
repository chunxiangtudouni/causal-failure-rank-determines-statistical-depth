module

public import Structure.PSTR_CurrentRecordSlice_147
public import Common.PSTR_TM_Codec_001

/-! Exact producers for the ORIGINAL TABLE planner's two encoded streams.
The first count is always large enough for the existing real bootstrap;
the second is empty or has at least four Datums. These facts follow from
the original input and SAME actual record producer, not new eligibility.
No stream is replaced by generic-controller input or a supplied reply. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTablePlannerStreams

open RationalControllerComputation PSTRQueryRecords

variable {I : Instance}

def firstData (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) : List Datum :=
  [.natural I.stageCount, .natural I.toolCount] ++
    (List.finRange I.stageCount).flatMap (fun stage => rawExperiment (input.experiment stage)) ++
    rawContract C ++ [.rational budget] ++ rawSet available ++ encodeHistory history

theorem original_two_streams (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) (records : List Nat) :
    CompactPrice.plannerInput input C available budget history records =
      encode (firstData input C available budget history) ++ encode (records.map Datum.natural) := rfl

theorem first_count_room (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) :
    9 ≤ (firstData input C available budget history).length := by
  simp only [firstData, rawContract, encodeHistory, List.length_append,
    List.length_cons, List.length_nil]
  omega

theorem first_header_room (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) :
    4 ≤ natBits (firstData input C available budget history).length := by
  have room := first_count_room input C available budget history
  have bounded := PSTRTMCodec001.natBits_bound (firstData input C available budget history).length
  by_contra insufficient
  have small : natBits (firstData input C available budget history).length ≤ 3 := by omega
  have power := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) small
  norm_num at power
  omega

def queryCount (I : Instance) (history : List (VisibleEvent I)) : Nat :=
  min (historyCursor history) I.stageCount + if historyCursor history < I.stageCount then 1 else 0

theorem record_count (available : Finset I.Tool) (history : List (VisibleEvent I)) :
    (nativeRecords available history).length = 4 * queryCount I history := by
  have prefixSize := stageRecords_length I.compatibility
    (PA17L01HistoryPrefixStrategy002.stageUsed available history)
    0 (min (historyCursor history) I.stageCount) (by change 0 + min _ _ ≤ I.stageCount; omega)
  dsimp only [nativeRecords, queryCount]
  by_cases active : historyCursor history < I.stageCount
  · rw [ite_eq_left active, ite_eq_left active, List.length_append, prefixSize,
      stageWords_length I.compatibility _ _ (by change min _ _ ≤ I.stageCount; omega)]
    omega
  · rw [ite_eq_right active, ite_eq_right active, List.append_nil, prefixSize]
    omega

theorem second_count_zero_or_room (available : Finset I.Tool) (history : List (VisibleEvent I)) :
    (nativeRecords available history).length = 0 ∨ 4 ≤ (nativeRecords available history).length := by
  rw [record_count]
  omega

theorem current_record (available : Finset I.Tool) (history : List (VisibleEvent I))
    (active : historyCursor history < I.stageCount) :
    (nativeRecords available history).drop (4 * historyCursor history) =
      replyWords I.toolCount
        (PaperProofs.Structure.LaminarTree.CompactControllerClaims.callback I.toolCount I.compatibility
          ⟨historyCursor history, Nat.lt_succ_of_lt active⟩
          (PA17L01HistoryPrefixStrategy002.stageUsed available history (historyCursor history))) :=
  nativeRecords_current available history active

end PaperProofs.Common.Native.PSTRTablePlannerStreams
