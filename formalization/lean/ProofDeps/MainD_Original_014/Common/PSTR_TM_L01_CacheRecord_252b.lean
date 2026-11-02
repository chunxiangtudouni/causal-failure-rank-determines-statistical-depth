module
public import Common.PSTR_TM_L01_CacheRecord_252a
public import Common.PSTR_L01_RecordNavigation_004

/-! Only the current ACTUAL cache is linked to its actual four-word record.
The complete Prefix produces the cache and entry-used equality; none is
an extra original assumption. Physical records retain the original frozen
145/146/147 same-heap/counts.take producer. No integer decoder is repeated. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTML01CacheRecord252
open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree CompactPrice PSTRStatistics.TableAlignment
open PA17L01HistoryPrefixStrategy002 PSTRQueryRecords PSTRTablePlannerStreams PSTRTableRecordDecision

variable {I : Instance}

def recordKindAtCache (records : List Nat) (cache : ReferenceReplayCache I) : Option ReferenceBudgetCase :=
  recordKind I.toolCount (recordAt records (historyCursor cache.seen))

def recordToolAtCache (records : List Nat) (cache : ReferenceReplayCache I) : Option I.Tool :=
  recordTool I.toolCount (recordAt records (historyCursor cache.seen))

def tableToolAtCache (available : Finset I.Tool) (cache : ReferenceReplayCache I) : Option I.Tool :=
  (referenceReplayStage I cache).bind (fun stage => (tableReply I available stage (historyUsed cache.entryHistory)).tool)

private theorem records_at_end (available : Finset I.Tool) (history : List (VisibleEvent I))
    (ended : I.stageCount ≤ historyCursor history) :
    recordAt (nativeRecords available history) (historyCursor history) = [] := by
  have inactive : ¬historyCursor history < I.stageCount := by omega
  have queries : queryCount I history = I.stageCount := by
    simp only [queryCount,Nat.min_eq_right ended,inactive,ite_false,Nat.add_zero]
  have length : (nativeRecords available history).length ≤ 4*historyCursor history := by
    rw [record_count,queries]
    omega
  simp only [recordAt,List.drop_eq_nil_of_le length,List.take_nil]

private theorem cache_record_decisions (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (s : State I) (cache : ReferenceReplayCache I)
    (laminar : LaminarSchedule I.compatibility)
    (aligned : TableStateAligned input available budget cache s)
    (used : ∀ stage : I.Stage, s.cursor = stage.val →
      historyUsed cache.entryHistory = toolsBefore s.history stage.val) :
    recordKindAtCache (nativeRecords available s.history) cache = tableKind I available cache ∧
      recordToolAtCache (nativeRecords available s.history) cache = tableToolAtCache available cache := by
  by_cases active : historyCursor s.history < I.stageCount
  · let stage : I.Stage := ⟨historyCursor s.history,active⟩
    have actualCursor : historyCursor s.history = s.cursor := by
      simpa only [aligned.seen] using aligned.cursor
    have cursor : s.cursor = stage.val := actualCursor.symm
    have currentStage := tableStateAligned_stage input available budget cache s aligned stage cursor
    have entry := used stage cursor
    have inside : historyCursor s.history < queryCount I s.history := by
      simp only [queryCount,Nat.min_eq_left active.le,active,ite_true]
      omega
    let answer := CompactControllerClaims.callback I.toolCount I.compatibility
      ⟨historyCursor s.history,Nat.lt_succ_of_lt active⟩
      (stageUsed available s.history (historyCursor s.history))
    have reply : tableReply I available stage (historyUsed cache.entryHistory) = answer := by
      dsimp only [tableReply,answer,stageUsed]
      rw [entry]
    have kind := native_record_kind available s.history laminar (historyCursor s.history) inside
    change recordKind I.toolCount (recordAt (nativeRecords available s.history) (historyCursor s.history)) =
      referenceCaseOfRanks answer.rank answer.bad at kind
    have tool := native_record_tool available s.history (historyCursor s.history) inside
    change recordTool I.toolCount (recordAt (nativeRecords available s.history) (historyCursor s.history)) = answer.tool at tool
    constructor
    · calc
        recordKindAtCache (nativeRecords available s.history) cache = referenceCaseOfRanks answer.rank answer.bad := by
          simpa only [recordKindAtCache,aligned.seen] using kind
        _ = tableKind I available cache := by
          simp only [tableKind,currentStage,Option.bind_eq_bind,Option.bind_some,reply]
    · calc
        recordToolAtCache (nativeRecords available s.history) cache = answer.tool := by
          simpa only [recordToolAtCache,aligned.seen] using tool
        _ = tableToolAtCache available cache := by
          simp only [tableToolAtCache,currentStage,Option.bind_some,reply]
  · have noStage : referenceReplayStage I cache = none := by
      unfold referenceReplayStage
      rw [aligned.seen]
      exact dite_eq_right active
    have empty := records_at_end available s.history (by omega)
    constructor
    · simp only [recordKindAtCache,aligned.seen,empty,recordKind,tableKind,noStage,Option.bind_eq_bind,Option.bind_none]
    · simp only [recordToolAtCache,aligned.seen,empty,recordTool,tableToolAtCache,noStage,Option.bind_none]

/-- Complete current-cache producer theorem. There is NO caller-supplied
cache alignment or recordsCorrect premise. End cursor N, failures, halted
and active clocks all retain the original none/tool/kind behavior. -/
theorem actual_cache_records (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1/2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s) :
    ∃ cache, TableStateAligned input available budget cache s ∧
      (∀ stage : I.Stage, s.cursor = stage.val → historyUsed cache.entryHistory = toolsBefore s.history stage.val) ∧
      recordKindAtCache (nativeRecords available s.history) cache = tableKind I available cache ∧
      recordToolAtCache (nativeRecords available s.history) cache = tableToolAtCache available cache := by
  obtain ⟨cache,aligned,used⟩ := actual_cache_entry input C laminar current accounting available budget positive small
    limit seed truth tapes hp
  obtain ⟨kind,tool⟩ := cache_record_decisions input available budget s cache laminar aligned used
  exact ⟨cache,aligned,used,kind,tool⟩

/-- Direct equations about the computed actual replay, convenient when
the caller already matches on tableReplay. No candidate-cache premise. -/
theorem actual_record_kind_eq (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1/2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s) :
    (tableReplay input available budget s.history).map (recordKindAtCache (nativeRecords available s.history)) =
      (tableReplay input available budget s.history).map (tableKind I available) := by
  obtain ⟨cache,aligned,_used,kind,_tool⟩ := actual_cache_records input C laminar current accounting available budget positive small
    limit seed truth tapes hp
  rw [aligned.parsed]
  exact congrArg some kind

theorem actual_record_tool_eq (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1/2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s) :
    (tableReplay input available budget s.history).map (recordToolAtCache (nativeRecords available s.history)) =
      (tableReplay input available budget s.history).map (tableToolAtCache available) := by
  obtain ⟨cache,aligned,_used,_kind,tool⟩ := actual_cache_records input C laminar current accounting available budget positive small
    limit seed truth tapes hp
  rw [aligned.parsed]
  exact congrArg some tool

end PaperProofs.Common.Native.PSTRTML01CacheRecord252
