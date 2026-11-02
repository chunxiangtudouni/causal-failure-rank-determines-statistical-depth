module

public import Common.PSTR_L01_RecordTool_003

/-! Navigate EVERY existing query record, including past replay stages.
The executable list selector and integer kind/tool decoders inspect only
the actual record stream. The proved producer remains the SAME persistent
Word execution. A real bit parser must still produce this representation. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTableRecordDecision

open PaperProofs.Statistics PaperProofs.Structure.LaminarTree
open PSTRQueryRecords PSTRTablePlannerStreams

def recordAt (records : List Nat) (index : Nat) : List Nat :=
  (records.drop (4 * index)).take 4

theorem drop_block (block rest : List Nat) (length : block.length = 4) (index : Nat) :
    (block ++ rest).drop (4 * (index + 1)) = rest.drop (4 * index) := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by rw [length]; omega), List.nil_append, length]
  congr 1

theorem stage_record_at {q : Nat} (full : List (Finset (Fin q))) (used : Nat → Finset (Fin q))
    (first count index : Nat) (after : List Nat) (inside : index < count)
    (bound : first + count ≤ full.length) :
    recordAt (stageRecords full used first count ++ after) index = stageWords full used (first + index) := by
  induction index generalizing first count with
  | zero =>
    cases count with
    | zero => omega
    | succ count =>
      rw [recordAt, stageRecords_succ, List.append_assoc, Nat.mul_zero, List.drop_zero, Nat.add_zero]
      exact List.take_left' (stageWords_length full used first (by omega))
  | succ index ih =>
    cases count with
    | zero => omega
    | succ count =>
      rw [recordAt, stageRecords_succ, List.append_assoc,
        drop_block _ _ (stageWords_length full used first (by omega)) index]
      have later := ih (first + 1) count (by omega) (by omega)
      have same : first + 1 + index = first + (index + 1) := by omega
      rw [same] at later
      exact later

theorem query_count_le {I : Instance} (history : List (VisibleEvent I)) : queryCount I history ≤ I.stageCount := by
  unfold queryCount
  by_cases active : historyCursor history < I.stageCount
  · rw [ite_eq_left active]
    omega
  · rw [ite_eq_right active]
    omega

theorem native_record_at {I : Instance} (available : Finset I.Tool) (history : List (VisibleEvent I))
    (index : Nat) (inside : index < queryCount I history) :
    recordAt (nativeRecords available history) index =
      stageWords I.compatibility (PA17L01HistoryPrefixStrategy002.stageUsed available history) index := by
  let count := min (historyCursor history) I.stageCount
  have room : count ≤ I.compatibility.length := Nat.min_le_right _ _
  dsimp only [nativeRecords]
  by_cases past : index < count
  · have selected := stage_record_at I.compatibility
      (PA17L01HistoryPrefixStrategy002.stageUsed available history) 0 count index
      (if historyCursor history < I.stageCount then
        stageWords I.compatibility (PA17L01HistoryPrefixStrategy002.stageUsed available history) count else [])
      past (by omega)
    simpa only [Nat.zero_add] using selected
  · have active : historyCursor history < I.stageCount := by
      unfold queryCount at inside
      by_contra inactive
      rw [ite_eq_right inactive] at inside
      omega
    have sameIndex : index = count := by
      unfold queryCount at inside
      rw [ite_eq_left active] at inside
      omega
    subst index
    rw [ite_eq_left active]
    have prefixSize := stageRecords_length I.compatibility
      (PA17L01HistoryPrefixStrategy002.stageUsed available history) 0 count (by omega)
    have wordSize := stageWords_length I.compatibility
      (PA17L01HistoryPrefixStrategy002.stageUsed available history) count room
    rw [recordAt, ← prefixSize, List.drop_left]
    exact List.take_of_length_le wordSize.le

theorem native_record_reply {I : Instance} (available : Finset I.Tool) (history : List (VisibleEvent I))
    (index : Nat) (inside : index < queryCount I history) :
    recordAt (nativeRecords available history) index =
      replyWords I.toolCount
        (CompactControllerClaims.callback I.toolCount I.compatibility
          ⟨index, by have := query_count_le history; change index < I.stageCount + 1; omega⟩
          (PA17L01HistoryPrefixStrategy002.stageUsed available history index)) := by
  rw [native_record_at available history index inside]
  exact stageWords_spec _ _ _ (by have := query_count_le history; change index < I.stageCount + 1; omega)

theorem native_record_kind {I : Instance} (available : Finset I.Tool) (history : List (VisibleEvent I))
    (laminar : LaminarSchedule I.compatibility) (index : Nat) (inside : index < queryCount I history) :
    let answer := CompactControllerClaims.callback I.toolCount I.compatibility
      ⟨index, by have := query_count_le history; change index < I.stageCount + 1; omega⟩
      (PA17L01HistoryPrefixStrategy002.stageUsed available history index)
    recordKind I.toolCount (recordAt (nativeRecords available history) index) =
      referenceCaseOfRanks answer.rank answer.bad := by
  dsimp only
  rw [native_record_reply available history index inside]
  have stageBound : index < I.compatibility.length := by
    have := query_count_le history
    change index < I.stageCount
    omega
  exact callback_record_kind I.toolCount I.compatibility laminar ⟨index, stageBound⟩ _

theorem native_record_tool {I : Instance} (available : Finset I.Tool) (history : List (VisibleEvent I))
    (index : Nat) (inside : index < queryCount I history) :
    recordTool I.toolCount (recordAt (nativeRecords available history) index) =
      (CompactControllerClaims.callback I.toolCount I.compatibility
        ⟨index, by have := query_count_le history; change index < I.stageCount + 1; omega⟩
        (PA17L01HistoryPrefixStrategy002.stageUsed available history index)).tool := by
  rw [native_record_reply available history index inside]
  exact record_tool_reply _ _

end PaperProofs.Common.Native.PSTRTableRecordDecision
