module
public import Common.PSTR_TM_L01_RecordReplay_253c

/-! The actual event fold uses FINAL records at EVERY earlier native
clock, and explicitly traverses the wrote/report middle cache. Its final
Prefix theorem supplies every pointwise simulation premise internally. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTML01RecordReplay253
open PaperProofs.Statistics PaperProofs.Structure PaperProofs.Structure.LaminarTree
open CompactPrice PSTRStatistics.TableAlignment PSTRQueryRecords PSTRTML01CacheRecord252

variable {I : Instance}

private theorem fold_one (input : StatisticalInput I) (available : Finset I.Tool)
    (risk : Rat) (records : List Nat) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (event : VisibleEvent I) (laminar : LaminarSchedule I.compatibility)
    (front : history.foldlM (recordStep input available risk records) (referenceReplayInitial I) =
      history.foldlM (tableStep input available risk) (referenceReplayInitial I))
    (parsed : history.foldlM (tableStep input available risk) (referenceReplayInitial I) = some cache)
    (kind : recordKindAtCache records cache = tableKind I available cache)
    (tool : recordToolAtCache records cache = tableToolAtCache available cache) :
    (history++[event]).foldlM (recordStep input available risk records) (referenceReplayInitial I) =
      (history++[event]).foldlM (tableStep input available risk) (referenceReplayInitial I) := by
  rw [List.foldlM_append,List.foldlM_append,front,parsed]
  simp only [Option.bind_eq_bind,Option.bind_some,List.foldlM_cons,List.foldlM_nil]
  rw [recordStep_eq_tableStep input available risk records cache event laminar kind tool]

private theorem fold_write_packet (input : StatisticalInput I) (available : Finset I.Tool)
    (risk : Rat) (records : List Nat) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (i : I.Stage) (bit truth : Bool) (serial : Nat) (laminar : LaminarSchedule I.compatibility)
    (front : history.foldlM (recordStep input available risk records) (referenceReplayInitial I) =
      history.foldlM (tableStep input available risk) (referenceReplayInitial I))
    (parsed : history.foldlM (tableStep input available risk) (referenceReplayInitial I) = some cache)
    (kind : recordKindAtCache records cache = tableKind I available cache)
    (tool : recordToolAtCache records cache = tableToolAtCache available cache) :
    (history++[VisibleEvent.wrote i bit serial,VisibleEvent.report i truth serial]).foldlM
        (recordStep input available risk records) (referenceReplayInitial I) =
      (history++[VisibleEvent.wrote i bit serial,VisibleEvent.report i truth serial]).foldlM
        (tableStep input available risk) (referenceReplayInitial I) := by
  rw [List.foldlM_append,List.foldlM_append,front,parsed]
  simp only [Option.bind_eq_bind,Option.bind_some,List.foldlM_cons,List.foldlM_nil]
  rw [recordStep_eq_tableStep input available risk records cache (.wrote i bit serial) laminar kind tool]
  cases first : tableStep input available risk cache (.wrote i bit serial) with
  | none => simp only [Option.bind_none]
  | some middle =>
    have same := tableStep_wrote_state input available risk cache middle i bit serial first
    subst middle
    obtain ⟨middleKind,middleTool⟩ := afterWrite_decisions records available cache i bit serial kind tool
    simp only [Option.bind_some]
    rw [recordStep_eq_tableStep input available risk records (afterWrite cache i bit serial)
      (.report i truth serial) laminar middleKind middleTool]

theorem actual_final_record_fold (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1/2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {beforeClock finalClock : Nat} {before final : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes beforeClock before)
    (hq : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes finalClock final)
    (ordered : beforeClock ≤ finalClock) :
    before.history.foldlM (recordStep input available budget (nativeRecords available final.history))
        (referenceReplayInitial I) =
      before.history.foldlM (tableStep input available budget) (referenceReplayInitial I) := by
  revert ordered
  induction hp with
  | initial => intro _; rfl
  | @next clock state next earlier step ih =>
    intro ordered
    have oldOrder : clock ≤ finalClock := by omega
    obtain ⟨cache,aligned,kind,tool⟩ := actual_final_cache_records input C laminar current accounting
      available budget positive small limit seed truth tapes earlier hq oldOrder
    have front := ih oldOrder
    have parsed := (PSTRStatistics.tableReplay_some_spec input available budget state.history cache aligned.parsed).2.1
    have one := fold_one input available budget (nativeRecords available final.history)
      state.history cache
    have two := fold_write_packet input available budget (nativeRecords available final.history)
      state.history cache
    generalize actionEq : tableRule input available budget limit seed state.history = action at step
    cases step with
    | review i live port resources =>
      exact one (.observation i (tapes i (state.ledger.reviews i).toNat).val) laminar front parsed kind tool
    | write i bit live port resources =>
      simpa only [record,writeResponses,current.1,ite_true,writeLedger,List.singleton_append] using
        two i bit (state.ledger.truth i) state.clock laminar front parsed kind tool
    | allocate handle selected active valid compatible unused unallocated window resources =>
      exact one (.committed handle selected) laminar front parsed kind tool
    | execute handle selected active valid compatible committed unused uncorrected window resources =>
      exact one (.executed handle selected) laminar front parsed kind tool
    | advance i live written resources =>
      exact one (.advanced i) laminar front parsed kind tool
    | stop active =>
      simpa only [stopState,Bool.false_eq_true,ite_false] using one .stopped laminar front parsed kind tool
    | abandon active =>
      simpa only [stopState,ite_true] using one .abandoned laminar front parsed kind tool

def recordReplay (input : StatisticalInput I) (available : Finset I.Tool) (risk : Rat)
    (records : List Nat) (history : List (VisibleEvent I)) : Option (ReferenceReplayCache I) := do
  if 0 < risk ∧ risk ≤ 1/2 then pure () else none
  let cache ← history.foldlM (recordStep input available risk records) (referenceReplayInitial I)
  if cache.phase ≠ .written ∧ cache.events.length ≤ I.stageCount ∧
      historyCursor cache.seen ≤ I.stageCount ∧ cache.seen = history then some cache else none

/-- The original Prefix produces ALL record simulation facts; recordsCorrect,
cache alignment, eventual success and H0 are NOT original premises. -/
theorem actual_final_record_replay (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1/2) (limit : ReferenceObservationLimit I)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {beforeClock finalClock : Nat} {before final : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes beforeClock before)
    (hq : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes finalClock final)
    (ordered : beforeClock ≤ finalClock) :
    recordReplay input available budget (nativeRecords available final.history) before.history =
      tableReplay input available budget before.history := by
  unfold recordReplay tableReplay
  rw [actual_final_record_fold input C laminar current accounting available budget positive small
    limit seed truth tapes hp hq ordered]

end PaperProofs.Common.Native.PSTRTML01RecordReplay253
