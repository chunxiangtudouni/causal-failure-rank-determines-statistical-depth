module

public import Common.PSTR_L01_PlannerStreams_001
public import Common.PSTR_SYM_FirstStreamPolynomial_069

/-! Thin actual application of the parent's frozen ORIGINAL planner
schema/count producer. No duplicate room proof or supplied firstData is
introduced. This stops at the FIRST footer and preserves ALL real record
encoding, even records=[], rather than claiming a global blank EOF. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPlannerParser

open PaperProofs.Common Turing PSTRTMIncrement009 PSTRSymbolicRawLoop PSTRSymbolicCursorArchive

theorem actual_original_planner_first {I : Instance} (input : StatisticalInput I) (contract : Contract I)
    (available : Finset I.Tool) (budget : Rat) (history : List (VisibleEvent I)) (records : List Nat) :
    ∃ (digits : List Bool) (trace : List (MachineState loopSupport.card)) (final : MachineState loopSupport.card),
      Runs rawLoopMachine (CompactPrice.plannerInput input contract available budget history records) trace final ∧
      final.Tape = archiveTape (PSTRTablePlannerStreams.firstData input contract available budget history) [] digits
        (encode (records.map Datum.natural)) true ∧
      final.Tape.head = true ∧ final.Tape.right = ListBlank.mk (encode (records.map Datum.natural)) ∧
      valueDigits digits = 0 ∧ 3 ≤ digits.length ∧
      trace.length ≤ 4096 * ((CompactPrice.plannerInput input contract available budget history records).length + 1)^3 ∧
      ∀ clock, visitedSpace rawLoopMachine
        (CompactPrice.plannerInput input contract available budget history records).length (trace.take clock) ≤
        16384 * ((CompactPrice.plannerInput input contract available budget history records).length + 1)^3 := by
  let data := PSTRTablePlannerStreams.firstData input contract available budget history
  let remaining := data.tail.tail
  have shape : streamData I.stageCount I.toolCount remaining = data := rfl
  have count := PSTRTablePlannerStreams.first_count_room input contract available budget history
  change 9 ≤ data.length at count
  have length := congrArg List.length shape
  simp only [streamData,List.length_cons] at length
  have room : 2 ≤ remaining.length := by omega
  obtain ⟨digits,trace,final,actual,tape,head,right,value,width,time,space⟩ :=
    actual_first_stream I.stageCount I.toolCount remaining (encode (records.map Datum.natural)) room
  rw [shape] at actual tape time space
  dsimp only [data] at actual tape time space
  rw [← PSTRTablePlannerStreams.original_two_streams input contract available budget history records] at actual time space
  exact ⟨digits,trace,final,actual,tape,head,right,value,width,time,space⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPlannerParser
