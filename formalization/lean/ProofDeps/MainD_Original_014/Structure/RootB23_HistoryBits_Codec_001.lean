module

public import Common.PSTR_TM_NativeEventBits_220

/-! Bit accounting for the original native-controller input codec.  These
lemmas count the original encoded fields, including both list-length headers.
They introduce neither a machine nor a validity certificate in its input. -/

@[expose] public section

namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23HistoryBits

open PSTRTMLength004 PSTRTMNativeEventBits220

variable {I : Instance}

def payloadBits (data : List Datum) : Nat := (data.map datumBits).sum

theorem natBits_le_value_add_one (value : Nat) : natBits value ≤ value + 1 := by
  simpa only [natBits, Nat.log2_eq_log_two] using
    Nat.add_le_add_right (Nat.log_le_self 2 value) 1

theorem list_length_le_payloadBits (data : List Datum) : data.length ≤ payloadBits data := by
  induction data with
  | nil => simp [payloadBits]
  | cons item later ih =>
    have positive := datumBits_pos item
    simp only [payloadBits, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

theorem payloadBits_le_encode_length (data : List Datum) :
    payloadBits data ≤ (encode data).length := by
  rw [encode_length]
  unfold payloadBits
  omega

theorem list_length_le_encode_length (data : List Datum) :
    data.length ≤ (encode data).length :=
  (list_length_le_payloadBits data).trans (payloadBits_le_encode_length data)

theorem rawSet_length {q : Nat} (available : Finset (Fin q)) :
    (rawSet available).length = q := by
  simp only [rawSet, List.length_map, List.length_finRange]

theorem rawSet_payloadBits {q : Nat} (available : Finset (Fin q)) :
    payloadBits (rawSet available) = 4 * q := by
  unfold payloadBits rawSet
  simp only [List.map_map, Function.comp_def, boolDatum_bits]
  simp [Nat.mul_comm]

/-- The outer controller list header is charged as well as the inner history
event count.  The final true delimiter and all late-report events are retained. -/
theorem controllerInput_length_le_payload (input : StatisticalInput I) (C : Contract I)
    (available : Finset I.Tool) (budget : Rat) (history : List (VisibleEvent I)) :
    (controllerInput input C available budget history).length ≤
      3 * (preparationInput input C budget).length + 6 * I.toolCount +
        10 * history.length + 10 + payloadBits (history.flatMap encodeEvent) := by
  let base := rawInstance input ++ rawContract C ++ [.rational budget]
  let events := history.flatMap encodeEvent
  have baseLength : base.length ≤ (preparationInput input C budget).length :=
    list_length_le_encode_length base
  have basePayload : payloadBits base ≤ (preparationInput input C budget).length :=
    payloadBits_le_encode_length base
  have arity : events.length ≤ 4 * history.length := history_event_arity_le history
  have header := natBits_le_value_add_one
    (base.length + I.toolCount + (events.length + 1))
  have historyHeader := natBits_le_value_add_one history.length
  have exactLength :
      (controllerInput input C available budget history).length =
        2 * natBits (base.length + I.toolCount + (events.length + 1)) + 2 +
          (payloadBits base + 4 * I.toolCount +
            (2 * natBits history.length + 2 + payloadBits events)) := by
    change (encode (base ++ rawSet available ++ encodeHistory history)).length = _
    rw [encode_length]
    simp only [List.length_append, rawSet_length, encodeHistory, List.length_cons,
      List.map_append, List.sum_append, List.map_cons, List.sum_cons, datumBits]
    rw [show ((rawSet available).map datumBits).sum = 4 * I.toolCount from
      rawSet_payloadBits available]
    rfl
  rw [exactLength]
  change _ ≤ 3 * _ + 6 * _ + 10 * _ + 10 + payloadBits events
  omega

end PaperProofs.Common.Native.RationalControllerComputation.RootB23HistoryBits
