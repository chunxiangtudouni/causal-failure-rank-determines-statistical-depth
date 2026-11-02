module

public import Common.PSTR_L01_RecordPlanner_005

/-! The actual Prefix produces every local refinement equality. No cache,
reply correctness, success, H0 or parser-certificate premise is supplied by
the original caller. This is action semantics, not a Boolean runtime bound. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTableRecordPlanner

open PaperProofs.Statistics PaperProofs.Structure PaperProofs.Structure.LaminarTree
open CompactPrice PSTRQueryRecords PSTRTML01CacheRecord252 PSTRStatistics.TableAlignment

variable {I : Instance}

theorem actual_prefix_rule (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (positive : 0 < budget) (small : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {state : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n state) :
    ∃ cache, TableStateAligned input available budget cache state ∧
      recordRuleFromCache input budget limit state.history (nativeRecords available state.history) cache =
        tableRule input available budget limit () state.history := by
  obtain ⟨cache, aligned, _used, kind, tool⟩ := actual_cache_records input C laminar current accounting
    available budget positive small limit seed truth tapes hp
  exact ⟨cache, aligned, record_rule_eq input available budget limit state.history
    (nativeRecords available state.history) cache aligned.parsed kind tool⟩

theorem actual_prefix_rule_computed (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (positive : 0 < budget) (small : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {state : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n state) :
    (tableReplay input available budget state.history).map
      (recordRuleFromCache input budget limit state.history (nativeRecords available state.history)) =
        some (tableRule input available budget limit () state.history) := by
  obtain ⟨cache, aligned, same⟩ := actual_prefix_rule input C laminar current accounting available budget
    positive small limit seed truth tapes hp
  rw [aligned.parsed, Option.map_some, same]

end PaperProofs.Common.Native.PSTRTableRecordPlanner

