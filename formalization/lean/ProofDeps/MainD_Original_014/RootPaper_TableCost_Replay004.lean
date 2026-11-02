module

public import RootPaper_TableCost_Step003

/-! A TABLE-specific replay returning its value and work on the same
recursive branches. A failed step keeps all work already performed and
never visits the remaining history. Budget/final guards are paid too. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootPaper.TableCost

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open CompactPrice PSTRTML01RecordReplay253

variable {I : Instance}

/-- One unit for every emitted primitive/access/guard record, together
with the copies and local control steps of the same evaluation. -/
def Execution.units (run : Execution I) : Nat :=
  run.calls.length+run.rationalTests.length+run.naturalTests.length+
    run.archiveReads.length+run.historyReads.length+run.copied+run.localTicks

theorem step_units (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (cache : ReferenceReplayCache I) (event : VisibleEvent I) :
    (step input available budget records cache event).units ≤
      60*(cache.seen.length+cache.events.length+1) := by
  have a:=kernel_counts budget records cache
  have b:=body_counts input available cache event (kernel budget records cache)
  simp only [Execution.units,step,List.length_append,List.length_cons,List.length_nil]
  omega

def join (front later : Execution I) : Execution I :=
  ⟨later.result,front.calls++later.calls,front.rationalTests++later.rationalTests,
    front.naturalTests++later.naturalTests,front.archiveReads++later.archiveReads,
    front.historyReads++later.historyReads,front.copied+later.copied,front.localTicks+later.localTicks+1⟩

theorem join_units (front later : Execution I) :
    (join front later).units=front.units+later.units+1 := by
  simp only [Execution.units,join,List.length_append]
  omega

def replayFrom (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat) (records : List Nat)
    (cache : ReferenceReplayCache I) : List (VisibleEvent I) → Execution I
  | [] => ⟨some cache,[],[],[],[],[],0,1⟩
  | event::later =>
      let front:=step input available budget records cache event
      match front.result with
      | none => {front with localTicks:=front.localTicks+1}
      | some next => join front (replayFrom input available budget records next later)

theorem replayFrom_result (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (cache : ReferenceReplayCache I) (history : List (VisibleEvent I)) :
    (replayFrom input available budget records cache history).result=
      history.foldlM (recordStep input available budget records) cache := by
  induction history generalizing cache with
  | nil => rfl
  | cons event later ih =>
      rw [List.foldlM_cons,←step_result input available budget records cache event]
      simp only [replayFrom]
      cases actual:(step input available budget records cache event).result <;>
        simp only [Option.bind_eq_bind,Option.bind_none,Option.bind_some,join,ih]

def replay (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (records : List Nat) (history : List (VisibleEvent I)) : Execution I :=
  let budgetTests:=[(budget,0),(budget,1/2)]
  if 0<budget ∧ budget≤1/2 then
    let run:=replayFrom input available budget records (referenceReplayInitial I) history
    match run.result with
    | none => {run with rationalTests:=budgetTests++run.rationalTests,localTicks:=run.localTicks+6}
    | some cache =>
        let cursor:=historyCursor cache.seen
        let result:=if cache.phase≠.written ∧ cache.events.length≤I.stageCount ∧ cursor≤I.stageCount ∧ cache.seen=history
          then some cache else none
        {run with
          result:=result
          rationalTests:=budgetTests++run.rationalTests
          naturalTests:=run.naturalTests++[(cache.events.length,I.stageCount),(cursor,I.stageCount)]
          historyReads:=run.historyReads++[⟨.events,cache.events.length⟩,⟨.cursor,cache.seen.length⟩,
            ⟨.sameHistory,cache.seen.length+history.length⟩]
          localTicks:=run.localTicks+14}
  else ⟨none,[],budgetTests,[],[],[],0,6⟩

theorem replay_result (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (records : List Nat) (history : List (VisibleEvent I)) :
    (replay input available budget records history).result=recordReplay input available budget records history := by
  unfold replay recordReplay
  dsimp only
  split_ifs
  · rw [←replayFrom_result]
    cases (replayFrom input available budget records (referenceReplayInitial I) history).result <;> rfl
  · rfl

def CacheBound (limit : Nat) (cache : ReferenceReplayCache I) : Prop :=
  cache.seen.length≤limit ∧ cache.entryHistory.length≤limit ∧ cache.events.length≤limit

theorem step_cacheBound (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (limit : Nat) (bounded : CacheBound limit cache)
    (finished : (step input available budget records cache event).result=some next) : CacheBound (limit+1) next := by
  rw [step_result] at finished
  rcases bounded with ⟨seen,entry,events⟩
  by_cases stopped:cache.halted=true
  · simp only [recordStep,stopped,ite_true] at finished
    cases finished
  · have live:cache.halted=false:=Bool.eq_false_of_not_eq_true stopped
    cases event
    all_goals simp only [recordStep,live,Bool.false_eq_true,ite_false,Option.bind_eq_bind,
      Option.bind_eq_some_iff] at finished
    all_goals repeat' rcases finished with ⟨_,_,finished⟩
    all_goals split_ifs at finished
    all_goals cases Option.some.inj finished
    all_goals simp only [CacheBound,List.length_append,List.length_cons,List.length_nil]
    all_goals omega

theorem replayFrom_units (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (cache : ReferenceReplayCache I)
    (history : List (VisibleEvent I)) (limit : Nat) (bounded : CacheBound limit cache) :
    (replayFrom input available budget records cache history).units ≤
      128*(history.length+1)*(limit+history.length+1) := by
  induction history generalizing cache limit with
  | nil => simp only [replayFrom,Execution.units,List.length_nil];omega
  | cons event later ih =>
      have front:=step_units input available budget records cache event
      have frontBound : (step input available budget records cache event).units≤120*(limit+1) := by
        rcases bounded with ⟨seen,entry,events⟩
        omega
      unfold replayFrom
      dsimp only
      cases finished:(step input available budget records cache event).result with
      | none =>
          simp only [Execution.units,List.length_cons] at *
          nlinarith
      | some next =>
          rw [join_units]
          have tail:=ih next (limit+1) (step_cacheBound input available budget records cache next event limit bounded finished)
          simp only [List.length_cons]
          nlinarith

theorem replay_units (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (history : List (VisibleEvent I)) :
    (replay input available budget records history).units≤160*(history.length+1)^2 := by
  have initial : CacheBound 0 (referenceReplayInitial I) := by
    simp only [CacheBound,referenceReplayInitial,List.length_nil];omega
  have run:=replayFrom_units input available budget records (referenceReplayInitial I) history 0 initial
  unfold replay
  dsimp only
  split
  · cases finished:(replayFrom input available budget records (referenceReplayInitial I) history).result with
    | none =>
        simp only [Execution.units,List.length_append,List.length_cons,List.length_nil] at *
        nlinarith
    | some cache =>
        simp only [Execution.units,List.length_append,List.length_cons,List.length_nil] at *
        nlinarith
  · simp only [Execution.units,List.length_cons,List.length_nil]
    nlinarith

theorem cacheBound_mono (cache : ReferenceReplayCache I) {a b : Nat} (order : a≤b)
    (bounded : CacheBound a cache) : CacheBound b cache :=
  ⟨bounded.1.trans order,bounded.2.1.trans order,bounded.2.2.trans order⟩

theorem replayFrom_cacheBound (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (cache next : ReferenceReplayCache I)
    (history : List (VisibleEvent I)) (limit : Nat) (bounded : CacheBound limit cache)
    (finished : (replayFrom input available budget records cache history).result=some next) :
    CacheBound (limit+history.length) next := by
  induction history generalizing cache limit with
  | nil =>
      cases Option.some.inj finished
      simpa only [List.length_nil,Nat.add_zero] using bounded
  | cons event later ih =>
      simp only [replayFrom] at finished
      cases one:(step input available budget records cache event).result with
      | none => simp only [one] at finished;cases finished
      | some child =>
          simp only [one,join] at finished
          have result:=ih child (limit+1)
            (step_cacheBound input available budget records cache child event limit bounded one) finished
          simpa only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using result

theorem replay_cacheBound (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (finished : (replay input available budget records history).result=some cache) :
    CacheBound history.length cache := by
  have initial : CacheBound 0 (referenceReplayInitial I) := by
    simp only [CacheBound,referenceReplayInitial,List.length_nil];omega
  unfold replay at finished
  dsimp only at finished
  split at finished
  · cases run:(replayFrom input available budget records (referenceReplayInitial I) history).result with
    | none => simp only [run] at finished;cases finished
    | some next =>
        simp only [run] at finished
        split_ifs at finished
        · cases Option.some.inj finished
          simpa only [Nat.zero_add] using
            replayFrom_cacheBound input available budget records (referenceReplayInitial I) cache history 0 initial run
  · cases finished

end RootPaper.TableCost
