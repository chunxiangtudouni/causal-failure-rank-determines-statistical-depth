module
public import Common.PSTR_TM_L01_CacheRecord_252b
public import PaperProofs.Common.NativeCapTransfer

/-! Earlier records of a REAL native Prefix are stable under its REAL
extension. The proof uses old current-window stage bounds and Step, not a
record-correctness premise. It preserves the entire physical four-word
slice, hence both existing integer decoders and their exact tool tie. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTML01RecordReplay253
open PaperProofs.Statistics PaperProofs.Structure PaperProofs.Structure.LaminarTree
open CompactPrice PA17L01HistoryPrefixStrategy002
open PSTRQueryRecords PSTRTablePlannerStreams PSTRTableRecordDecision

variable {I : Instance} {Seed : Type*}

private theorem prefix_same_clock (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {clock : Nat} {left right : State I}
    (hl : Prefix input C mode accounting rule seed truth tapes clock left)
    (hr : Prefix input C mode accounting rule seed truth tapes clock right) : left = right := by
  exact (prefix_eq_run input C mode accounting rule seed truth tapes hl).symm.trans
    (prefix_eq_run input C mode accounting rule seed truth tapes hr)

theorem prefix_extension_tools (input : StatisticalInput I) (C : Contract I)
    (current : C.IsCurrentAllocation) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {beforeClock finalClock : Nat} {before final : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes beforeClock before)
    (hq : Prefix input C mode accounting rule seed truth tapes finalClock final)
    (ordered : beforeClock ≤ finalClock) :
    before.cursor ≤ final.cursor ∧
      ∀ index, index ≤ before.cursor → toolsBefore final.history index = toolsBefore before.history index := by
  induction hq generalizing beforeClock before with
  | initial =>
    have zero : beforeClock = 0 := by omega
    subst beforeClock
    have same := prefix_same_clock input C mode accounting rule seed truth tapes hp Prefix.initial
    cases same
    exact ⟨Nat.le_refl _,fun _ _ => rfl⟩
  | @next clock state next earlier step ih =>
    by_cases equal : beforeClock = clock+1
    · have hp' : Prefix input C mode accounting rule seed truth tapes (clock+1) before := by
        simpa only [equal] using hp
      have same := prefix_same_clock input C mode accounting rule seed truth tapes hp' (Prefix.next earlier step)
      cases same
      exact ⟨Nat.le_refl _,fun _ _ => rfl⟩
    · have order : beforeClock ≤ clock := by omega
      obtain ⟨cursor,stable⟩ := ih hp order
      refine ⟨cursor.trans (step_cursor_bounds input C mode accounting tapes step).1,?_⟩
      intro index inside
      calc
        toolsBefore next.history index = toolsBefore state.history index :=
          step_toolsBefore input C current.1 current.2 mode accounting tapes step index (inside.trans cursor)
        _ = toolsBefore before.history index := stable index inside

theorem query_count_eq_min (history : List (VisibleEvent I)) :
    queryCount I history = min (historyCursor history+1) I.stageCount := by
  unfold queryCount
  split_ifs with active
  · rw [Nat.min_eq_left (by omega),Nat.min_eq_left (by omega)]
  · rw [Nat.min_eq_right (by omega),Nat.min_eq_right (by omega)]
    omega

theorem query_count_mono {earlier later : List (VisibleEvent I)}
    (cursor : historyCursor earlier ≤ historyCursor later) : queryCount I earlier ≤ queryCount I later := by
  rw [query_count_eq_min,query_count_eq_min]
  omega

theorem record_at_ended (available : Finset I.Tool) (history : List (VisibleEvent I))
    (index : Nat) (ended : I.stageCount ≤ index) : recordAt (nativeRecords available history) index = [] := by
  have size : (nativeRecords available history).length ≤ 4*index := by
    rw [record_count]
    have bound := query_count_le history
    omega
  simp only [recordAt,List.drop_eq_nil_of_le size,List.take_nil]

theorem record_at_of_tools (available : Finset I.Tool)
    (earlier later : List (VisibleEvent I)) (cursor : historyCursor earlier ≤ historyCursor later)
    (index : Nat) (inside : index < queryCount I earlier)
    (used : toolsBefore later index = toolsBefore earlier index) :
    recordAt (nativeRecords available later) index = recordAt (nativeRecords available earlier) index := by
  have laterInside : index < queryCount I later := inside.trans_le (query_count_mono cursor)
  rw [native_record_at available later index laterInside,native_record_at available earlier index inside]
  have bound : index < I.compatibility.length+1 := by
    have h := query_count_le earlier
    change index < I.stageCount+1
    omega
  rw [stageWords_spec _ _ _ bound,stageWords_spec _ _ _ bound]
  have same : stageUsed available later index = stageUsed available earlier index := by
    unfold stageUsed
    rw [used]
  rw [same]

theorem actual_record_stable (input : StatisticalInput I) (C : Contract I)
    (current : C.IsCurrentAllocation) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {beforeClock finalClock : Nat} {before final : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes beforeClock before)
    (hq : Prefix input C mode accounting rule seed truth tapes finalClock final)
    (ordered : beforeClock ≤ finalClock) (available : Finset I.Tool)
    (index : Nat) (inside : index < queryCount I before.history) :
    recordAt (nativeRecords available final.history) index = recordAt (nativeRecords available before.history) index := by
  obtain ⟨cursor,stable⟩ := prefix_extension_tools input C current mode accounting rule seed truth tapes hp hq ordered
  have oldCursor := prefix_historyCursor input C mode accounting rule seed truth tapes hp
  have newCursor := prefix_historyCursor input C mode accounting rule seed truth tapes hq
  have indexBound : index ≤ before.cursor := by
    rw [query_count_eq_min] at inside
    have bound := Nat.min_le_left (historyCursor before.history+1) I.stageCount
    omega
  apply record_at_of_tools available before.history final.history (by omega) index inside
  exact stable index indexBound

theorem actual_cursor_record_stable (input : StatisticalInput I) (C : Contract I)
    (current : C.IsCurrentAllocation) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {beforeClock finalClock : Nat} {before final : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes beforeClock before)
    (hq : Prefix input C mode accounting rule seed truth tapes finalClock final)
    (ordered : beforeClock ≤ finalClock) (available : Finset I.Tool) :
    recordAt (nativeRecords available final.history) (historyCursor before.history) =
      recordAt (nativeRecords available before.history) (historyCursor before.history) := by
  by_cases active : historyCursor before.history < I.stageCount
  · apply actual_record_stable input C current mode accounting rule seed truth tapes hp hq ordered available
    rw [query_count_eq_min,Nat.min_eq_left (by omega)]
    omega
  · rw [record_at_ended available final.history _ (by omega),
      record_at_ended available before.history _ (by omega)]

end PaperProofs.Common.Native.PSTRTML01RecordReplay253
