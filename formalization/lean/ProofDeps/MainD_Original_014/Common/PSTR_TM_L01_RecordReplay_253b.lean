module
public import Common.PSTR_TM_L01_RecordReplay_253a

/-! FINAL actual records may be reused at every EARLIER actual cache.
The earlier cache is produced from a real Prefix by252; its callback is
then transported by253a's entire-slice stability. A write/report's middle
cache is treated explicitly, since it is NOT itself a native clock Prefix. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTML01RecordReplay253
open PaperProofs.Statistics PaperProofs.Structure PaperProofs.Structure.LaminarTree
open CompactPrice PSTRStatistics.TableAlignment PA17L01HistoryPrefixStrategy002
open PSTRQueryRecords PSTRTML01CacheRecord252

variable {I : Instance}

theorem actual_final_cache_records (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1/2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {beforeClock finalClock : Nat} {before final : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes beforeClock before)
    (hq : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes finalClock final)
    (ordered : beforeClock ≤ finalClock) :
    ∃ cache, TableStateAligned input available budget cache before ∧
      recordKindAtCache (nativeRecords available final.history) cache = tableKind I available cache ∧
      recordToolAtCache (nativeRecords available final.history) cache = tableToolAtCache available cache := by
  obtain ⟨cache,aligned,_used,kind,tool⟩ := actual_cache_records input C laminar current accounting
    available budget positive small limit seed truth tapes hp
  have stable := actual_cursor_record_stable input C current .uncapped accounting
    (tableRule input available budget limit) seed truth tapes hp hq ordered available
  refine ⟨cache,aligned,?_,?_⟩
  · calc
      recordKindAtCache (nativeRecords available final.history) cache =
          recordKindAtCache (nativeRecords available before.history) cache := by
        unfold recordKindAtCache
        rw [aligned.seen,stable]
      _ = tableKind I available cache := kind
  · calc
      recordToolAtCache (nativeRecords available final.history) cache =
          recordToolAtCache (nativeRecords available before.history) cache := by
        unfold recordToolAtCache
        rw [aligned.seen,stable]
      _ = tableToolAtCache available cache := tool

theorem actual_final_kind_map (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1/2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {beforeClock finalClock : Nat} {before final : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes beforeClock before)
    (hq : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes finalClock final)
    (ordered : beforeClock ≤ finalClock) :
    (tableReplay input available budget before.history).map (recordKindAtCache (nativeRecords available final.history)) =
      (tableReplay input available budget before.history).map (tableKind I available) := by
  obtain ⟨cache,aligned,kind,_tool⟩ := actual_final_cache_records input C laminar current accounting
    available budget positive small limit seed truth tapes hp hq ordered
  rw [aligned.parsed]
  exact congrArg some kind

theorem actual_final_tool_map (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1/2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {beforeClock finalClock : Nat} {before final : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes beforeClock before)
    (hq : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes finalClock final)
    (ordered : beforeClock ≤ finalClock) :
    (tableReplay input available budget before.history).map (recordToolAtCache (nativeRecords available final.history)) =
      (tableReplay input available budget before.history).map (tableToolAtCache available) := by
  obtain ⟨cache,aligned,_kind,tool⟩ := actual_final_cache_records input C laminar current accounting
    available budget positive small limit seed truth tapes hp hq ordered
  rw [aligned.parsed]
  exact congrArg some tool

/-- The real wrote/report boundary is a second event within one native
write Step. It changes neither the lookup cursor nor the entry snapshot. -/
def afterWrite (cache : ReferenceReplayCache I) (stage : I.Stage) (bit : Bool) (serial : Nat) : ReferenceReplayCache I :=
  { cache with seen := cache.seen++[.wrote stage bit serial],phase := .written }

theorem afterWrite_cursor (cache : ReferenceReplayCache I) (stage : I.Stage) (bit : Bool) (serial : Nat) :
    historyCursor (afterWrite cache stage bit serial).seen = historyCursor cache.seen := by
  simp [afterWrite,historyCursor,List.filterMap_append,eventAdvance]

theorem afterWrite_stage (cache : ReferenceReplayCache I) (stage : I.Stage) (bit : Bool) (serial : Nat) :
    referenceReplayStage I (afterWrite cache stage bit serial) = referenceReplayStage I cache := by
  unfold referenceReplayStage
  rw [afterWrite_cursor]

theorem afterWrite_decisions (records : List Nat) (available : Finset I.Tool)
    (cache : ReferenceReplayCache I) (stage : I.Stage) (bit : Bool) (serial : Nat)
    (kind : recordKindAtCache records cache = tableKind I available cache)
    (tool : recordToolAtCache records cache = tableToolAtCache available cache) :
    recordKindAtCache records (afterWrite cache stage bit serial) = tableKind I available (afterWrite cache stage bit serial) ∧
    recordToolAtCache records (afterWrite cache stage bit serial) = tableToolAtCache available (afterWrite cache stage bit serial) := by
  have recordKind : recordKindAtCache records (afterWrite cache stage bit serial) = recordKindAtCache records cache := by
    unfold recordKindAtCache
    rw [afterWrite_cursor]
  have recordTool : recordToolAtCache records (afterWrite cache stage bit serial) = recordToolAtCache records cache := by
    unfold recordToolAtCache
    rw [afterWrite_cursor]
  have sameKind : tableKind I available (afterWrite cache stage bit serial) = tableKind I available cache := by
    unfold tableKind
    rw [afterWrite_stage]
    rfl
  have sameTool : tableToolAtCache available (afterWrite cache stage bit serial) = tableToolAtCache available cache := by
    unfold tableToolAtCache
    rw [afterWrite_stage]
    rfl
  exact ⟨recordKind.trans (kind.trans sameKind.symm),recordTool.trans (tool.trans sameTool.symm)⟩

end PaperProofs.Common.Native.PSTRTML01RecordReplay253
