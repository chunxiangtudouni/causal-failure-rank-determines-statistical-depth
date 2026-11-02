module
public import Common.PSTR_TM_L01_RecordReplay_253d

/-! The record-only cache itself is returned from the original actual
Prefix. No correct-record/cache certificate is an original input. This
is a semantic executable fold, not a claimed Bool compilation/cost bound. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTML01RecordReplay253
open PaperProofs.Statistics PaperProofs.Structure PaperProofs.Structure.LaminarTree
open CompactPrice PSTRStatistics.TableAlignment PSTRQueryRecords PSTRTML01CacheRecord252

variable {I : Instance}

theorem actual_final_record_cache (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1/2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {beforeClock finalClock : Nat} {before final : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes beforeClock before)
    (hq : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes finalClock final)
    (ordered : beforeClock ≤ finalClock) :
    ∃ cache, recordReplay input available budget (nativeRecords available final.history) before.history = some cache ∧
      TableStateAligned input available budget cache before ∧
      recordKindAtCache (nativeRecords available final.history) cache = tableKind I available cache ∧
      recordToolAtCache (nativeRecords available final.history) cache = tableToolAtCache available cache := by
  obtain ⟨cache,aligned,kind,tool⟩ := actual_final_cache_records input C laminar current accounting
    available budget positive small limit seed truth tapes hp hq ordered
  refine ⟨cache,?_,aligned,kind,tool⟩
  rw [actual_final_record_replay input C laminar current accounting available budget positive small
    limit seed truth tapes hp hq ordered]
  exact aligned.parsed

/-- Self-final specialization: the runtime fold receives precisely the
actual record stream at this caller's history, not a future answer oracle. -/
theorem actual_record_cache (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1/2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {clock : Nat} {state : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes clock state) :
    ∃ cache, recordReplay input available budget (nativeRecords available state.history) state.history = some cache ∧
      TableStateAligned input available budget cache state ∧
      recordKindAtCache (nativeRecords available state.history) cache = tableKind I available cache ∧
      recordToolAtCache (nativeRecords available state.history) cache = tableToolAtCache available cache := by
  exact actual_final_record_cache input C laminar current accounting available budget positive small
    limit seed truth tapes hp hp (Nat.le_refl _)

end PaperProofs.Common.Native.PSTRTML01RecordReplay253
