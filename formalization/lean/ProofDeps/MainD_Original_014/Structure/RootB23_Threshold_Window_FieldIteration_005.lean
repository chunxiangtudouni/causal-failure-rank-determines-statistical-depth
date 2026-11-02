module

public import Structure.RootB23_Threshold_Window_FieldMachine_004

@[expose] public section

namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

open Turing PSTRTMSeq005 PA17TMDivisionCompose006

/-- The actual nested invocation and all real mark/scan/return/restore steps.
This internal composition consumes one run of its fixed inner program. The
closed power producer will supply it recursively, down to the actual013 gap
expander; no such run is an original-input hypothesis. -/
theorem field_iteration {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (left before after : List Bool) (remaining : Nat)
    (inner : List (MachineState states))
    (innerRun : RunsFrom body
      ⟨0, Tape.mk₂ (false :: false :: (marks remaining ++ false :: false :: left)) before⟩
      inner
      ⟨exit, Tape.mk₂ (false :: false :: (marks remaining ++ false :: false :: left)) after⟩) :
    ∃ trace, Segment (fieldMachine body exit)
      (controlLift (controlState 0 left (pairs true (remaining + 1) ++ false :: false :: before)))
      trace
      (controlLift (controlState 12 (false :: left)
        (true :: (pairs true remaining ++ false :: false :: after)))) ∧
      trace.length = 5 * remaining + 15 + inner.length := by
  let entered := fieldEnterTrace left before remaining
  let returned := fieldReturnTrace (marks remaining ++ false :: false :: left) after
  let home := gapHomeTrace true (false :: left) (false :: false :: after) remaining
  let restored := fieldRestoreTrace left (pairs true remaining ++ false :: false :: after)
  have enterRun := fieldEnter_runsFrom left before remaining
  have returnRun := fieldReturn_runsFrom (marks remaining ++ false :: false :: left) after
  have homeRun := gapHome_runsFrom true (false :: left) (false :: false :: after) remaining
  have restoreSegment := fieldRestore_segment left (pairs true remaining ++ false :: false :: after)
  have enterSegment := control_lift_segment body exit _ _ _
    (show Segment fieldControl _ entered _ from ⟨enterRun.1, enterRun.2.1, enterRun.2.2.1⟩)
  have innerSegment := body_lift_segment body exit _ _ _ innerRun
  have returnSegment := control_lift_segment body exit _ _ _
    (show Segment fieldControl _ returned _ from ⟨returnRun.1, returnRun.2.1, returnRun.2.2.1⟩)
  have homeSegment := home_lift_segment body exit 2 (Or.inl rfl) _ _ _ homeRun
  have restoreGlobal := control_lift_segment body exit _ _ restored restoreSegment
  have enterTransfer := control_to_body body exit
    (Tape.mk₂ (false :: false :: (marks remaining ++ false :: false :: left)) before)
  have returnTransfer := body_to_return body exit _ innerRun.2.2.2
  have homeTransfer := control_to_home body exit 2 9 (Or.inl ⟨rfl, rfl⟩)
    (Tape.mk₂ (marks remaining ++ false :: false :: left) (false :: false :: after))
  have restoreTransfer := home_to_restore body exit
    (Tape.mk₂ (false :: false :: left) (pairs true remaining ++ false :: false :: after))
  have joined1 := segment_append (fieldMachine body exit) _ _ _ _ _ _
    enterSegment innerSegment enterTransfer
  have joined2 := segment_append (fieldMachine body exit) _ _ _ _ _ _
    joined1 returnSegment returnTransfer
  have joined3 := segment_append (fieldMachine body exit) _ _ _ _ _ _
    joined2 homeSegment homeTransfer
  have joined4 := segment_append (fieldMachine body exit) _ _ _ _ _ _
    joined3 restoreGlobal restoreTransfer
  refine ⟨(((entered.map controlLift ++ inner.map bodyLift) ++ returned.map controlLift) ++
      home.map (homeLift 2)) ++ restored.map controlLift, joined4, ?_⟩
  simp only [List.length_append, List.length_map, entered, returned, home, restored,
    fieldEnter_length, fieldReturnTrace, gapHome_length, fieldRestoreTrace,
    List.length_cons, List.length_nil]
  omega

theorem field_iteration_next {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (left work : List Bool) :
    TM0.step (fieldMachine body exit) (controlLift (controlState 12 (false :: left) (true :: work))) =
      some (controlLift (controlState 0 (true :: false :: left) work)) :=
  control_lift_step body exit _ _ (fieldRestore_next left work)

/-- At the genuine zero/end flag, the same program really returns over the
entire restored counter. Its final HALT is a static home-phase port. -/
theorem field_finish {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (archive work : List Bool) (done : Nat) :
    ∃ trace, RunsFrom (fieldMachine body exit)
      (controlLift (controlState 0 (marks done ++ false :: archive) (false :: false :: work)))
      trace
      (homeLift 3 (homeState 4 (false :: archive) (pairs true done ++ false :: false :: work))) ∧
      trace.length = 3 * done + 6 := by
  have finishRun := fieldFinish_runsFrom (marks done ++ false :: archive) work
  have homeRun := gapHome_runsFrom true archive (false :: false :: work) done
  have finishSegment := control_lift_segment body exit _ _ _
    (show Segment fieldControl _ _ _ from ⟨finishRun.1, finishRun.2.1, finishRun.2.2.1⟩)
  have homeSegment := home_lift_segment body exit 3 (Or.inr rfl) _ _ _ homeRun
  have transfer := control_to_home body exit 3 7 (Or.inr ⟨rfl, rfl⟩)
    (Tape.mk₂ (marks done ++ false :: archive) (false :: false :: work))
  have full := segment_append (fieldMachine body exit) _ _ _ _ _ _
    finishSegment homeSegment transfer
  refine ⟨(fieldFinishTrace (marks done ++ false :: archive) work).map controlLift ++
      (gapHomeTrace true archive (false :: false :: work) done).map (homeLift 3),
      segment_runsFrom _ _ _ _ full (final_home_halt body exit _), ?_⟩
  simp only [List.length_append, List.length_map, fieldFinishTrace, gapHome_length,
    List.length_cons, List.length_nil]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow
