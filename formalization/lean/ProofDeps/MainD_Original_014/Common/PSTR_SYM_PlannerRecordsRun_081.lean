module

public import Common.PSTR_SYM_DualStreamNative_080

/-! The internal zero-or-large packet condition is produced by the
ORIGINAL same-history nativeRecords. No record-length eligibility is
added to the original statistical input or to its TABLE planner call. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream

open PaperProofs.Common PaperProofs.Common.Native Turing PSTRTMIncrement009 PSTRQueryRecords

theorem record_end_right₀ (data : List Datum) (firstDigits : List Bool) (records : List Nat)
    (secondDigits : List Bool) :
    (recordEndTape data firstDigits records secondDigits).right₀ = ListBlank.mk [true] := by
  unfold recordEndTape
  split <;> rfl

theorem native_records_domain {I : Instance} (available : Finset I.Tool) (history : List (VisibleEvent I)) :
    nativeRecords available history = [] ∨ 4 ≤ (nativeRecords available history).length := by
  rcases PSTRTablePlannerStreams.second_count_zero_or_room available history with zero | large
  · exact Or.inl (List.eq_nil_of_length_eq_zero zero)
  · exact Or.inr large

theorem actual_native_records {I : Instance} (input : StatisticalInput I) (contract : Contract I)
    (available : Finset I.Tool) (budget : Rat) (history : List (VisibleEvent I)) :
    ∃ (firstDigits secondDigits : List Bool)
      (trace : List (MachineState dualSupport.card)) (final : MachineState dualSupport.card),
      Runs dualMachine (CompactPrice.plannerInput input contract available budget history
        (nativeRecords available history)) trace final ∧
      final.Tape = recordEndTape (PSTRTablePlannerStreams.firstData input contract available budget history)
        firstDigits (nativeRecords available history) secondDigits ∧
      final.Tape.head = true ∧ final.Tape.right = ListBlank.mk [] ∧
      valueDigits firstDigits = 0 ∧ 3 ≤ firstDigits.length ∧ valueDigits secondDigits = 0 ∧
      trace.length ≤ 16384 * ((CompactPrice.plannerInput input contract available budget history
        (nativeRecords available history)).length + 1)^3 ∧
      ∀ clock, visitedSpace dualMachine (CompactPrice.plannerInput input contract available budget history
        (nativeRecords available history)).length (trace.take clock) ≤
          65536 * ((CompactPrice.plannerInput input contract available budget history
            (nativeRecords available history)).length + 1)^3 := by
  exact actual_original_dual input contract available budget history (nativeRecords available history)
    (native_records_domain available history)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream
