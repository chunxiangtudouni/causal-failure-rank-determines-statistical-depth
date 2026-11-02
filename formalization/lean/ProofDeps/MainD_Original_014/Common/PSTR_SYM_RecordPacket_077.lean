module

public import Common.PSTR_SYM_DualStreamGateRun_076

/-! Exact physical packet/length facts needed by the ACTUAL positive
second-stream bootstrap/remaining composition. These budgets describe
existing code, not a new machine family or supplied parsed answer. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream

open Turing PSTRTMIncrement009 PSTRSymbolicRawBootstrap PSTRSymbolicRetainedBootstrap
open PSTRSymbolicRawLoop PSTRSymbolicLaneArchive PSTRSymbolicCursorArchive

theorem bootstrap_stream_bits (first second : Nat) (remaining : List Datum) (unread : List Bool) :
    bootstrapInput (streamData first second remaining).length first second
      (remaining.flatMap encodeDatum ++ true :: unread) =
        encode (streamData first second remaining) ++ unread := by
  simp only [bootstrapInput,encode,streamData,List.flatMap_cons,List.append_assoc,List.singleton_append]

theorem bootstrap_is_pending (archive : List Bool) (count first second : Nat)
    (remaining : List Datum) (unread : List Bool) :
    bootstrapTapeFrom archive count first second (remaining.flatMap encodeDatum ++ true :: unread) =
      pendingSuffix [.natural first,.natural second] archive (afterTwo count) remaining unread := by
  simp only [bootstrapTapeFrom,pendingSuffix,allDatumPairs_cells,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.reverse_append,List.append_assoc]

theorem bootstrap_cost_encoded (first second : Nat) (remaining : List Datum) :
    bootstrapCost (streamData first second remaining).length first second ≤
      1024 * ((encode (streamData first second remaining)).length + 1)^2 := by
  let data := streamData first second remaining
  let size := (encode data).length
  let count := data.length
  have parts : size = (encodeNat count).length + (encodeDatum (.natural first)).length +
      (encodeDatum (.natural second)).length + (remaining.flatMap encodeDatum).length + 1 := by
    simp only [size,encode,count,data,streamData,List.flatMap_cons,List.length_append,List.length_singleton]
    omega
  have header := PSTRTMLength004.encodeNat_length count
  have width : natBits count ≤ size := by omega
  have firstRoom : (encodeDatum (.natural first)).length ≤ size := by omega
  have secondRoom : (encodeDatum (.natural second)).length ≤ size := by omega
  have squareCount := Nat.pow_le_pow_left (Nat.add_le_add_right width 1) 2
  have squareFirst := Nat.pow_le_pow_left (Nat.add_le_add_right firstRoom 1) 2
  have squareSecond := Nat.pow_le_pow_left (Nat.add_le_add_right secondRoom 1) 2
  change bootstrapCost count first second ≤ 1024 * (size + 1)^2
  unfold bootstrapCost
  nlinarith [Nat.zero_le (size^2)]

theorem record_values_decompose (records : List Nat) (large : 4 ≤ records.length) :
    ∃ first second remaining, records = first :: second :: remaining ∧ 2 ≤ remaining.length := by
  cases records with
  | nil => simp only [List.length_nil] at large; omega
  | cons first later =>
    cases later with
    | nil => simp only [List.length_cons,List.length_nil] at large; omega
    | cons second remaining =>
      refine ⟨first,second,remaining,rfl,?_⟩
      simp only [List.length_cons] at large
      omega

theorem record_data_decompose (first second : Nat) (remaining : List Nat) :
    (first :: second :: remaining).map Datum.natural =
      streamData first second (remaining.map Datum.natural) := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream
