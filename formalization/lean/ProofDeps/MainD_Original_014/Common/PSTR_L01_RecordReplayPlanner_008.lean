module

public import Common.PSTR_L01_NativePlanner_007
public import Common.PSTR_TM_L01_RecordReplay_253e

/-! A logical planner whose executable replay and structural decisions read
the actual record stream. Its actual-Prefix theorem derives replay and all
record equalities internally. The component is not a Bool implementation:
raw archive parsing and the actual scalar arithmetic calls remain needed. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTableRecordPlanner

open PaperProofs.Statistics PaperProofs.Structure PaperProofs.Structure.LaminarTree
open CompactPrice PSTRQueryRecords PSTRTML01RecordReplay253

variable {I : Instance}

def recordPlanner (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I)) (records : List Nat) : Action I :=
  match recordReplay input available budget records history with
  | none => .abandon
  | some cache => recordRuleFromCache input budget limit history records cache

theorem actual_prefix_record_planner (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {clock : Nat} {state : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes clock state) :
    recordPlanner input available budget limit state.history (nativeRecords available state.history) =
      tableRule input available budget limit () state.history := by
  obtain ⟨cache, replay, aligned, kind, tool⟩ := actual_record_cache input C laminar current accounting
    available budget positive small limit seed truth tapes hp
  unfold recordPlanner
  rw [replay]
  exact record_rule_eq input available budget limit state.history (nativeRecords available state.history)
    cache aligned.parsed kind tool

end PaperProofs.Common.Native.PSTRTableRecordPlanner
