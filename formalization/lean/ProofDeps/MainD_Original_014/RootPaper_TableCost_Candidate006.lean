module

public import RootPaper_TableCost_Decision005

/-! A single result-producing TABLE candidate, with the very replay,
kernel, WORD operands, history navigation and bookkeeping it performed.
The action erases to candidate011 on every history; the existing actual
native theorem then identifies the unchanged selected native policy. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootPaper.TableCost
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open CompactPrice PSTRTableRecordPlanner PSTRQueryRecords PaperProofs.Structure.LaminarTree
variable {I : Instance}

theorem testing_units (input : StatisticalInput I) (limit : ReferenceObservationLimit I)
    (cache : ReferenceReplayCache I) (data : Kernel I) (stage : I.Stage) :
    (testing input limit cache data stage).units≤64*(cache.seen.length+1) := by
  have observations : (historyObservations cache.seen stage).length≤cache.seen.length :=
    List.length_filterMap_le _ _
  unfold testing
  cases data.kind with
  | none => simp only [bare,Decision.units,List.length_nil];omega
  | some kind =>
      cases kind with
      | infiniteRank => simp only [bare,Decision.units,List.length_nil];omega
      | noTool | finiteBad depth =>
          cases data.target with
          | none => simp only [bare,Decision.units,List.length_nil];omega
          | some target =>
              dsimp only
              cases limit
              all_goals split_ifs
              all_goals simp [Decision.units]
              all_goals omega

theorem decisionBody_units (input : StatisticalInput I) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I) (data : Kernel I) :
    (decisionBody input limit history cache data).units≤64*(cache.seen.length+history.length+1) := by
  unfold decisionBody
  cases cache.halted with
  | true => simp only [ite_true,bare,Decision.units,List.length_nil];omega
  | false =>
      simp only [Bool.false_eq_true,ite_false]
      cases stageAt data with
      | none => simp only [Decision.units,List.length_cons,List.length_nil];omega
      | some stage =>
          dsimp only
          cases cache.phase with
          | testing => exact (testing_units input limit cache data stage).trans (by omega)
          | written => simp only [bare,Decision.units,List.length_nil];omega
          | reported =>
              dsimp only
              split_ifs <;> simp only [Decision.units,List.length_cons,List.length_nil] <;> omega
          | allocated tool => simp only [Decision.units,List.length_cons,List.length_nil];omega
          | executed tool => simp only [bare,Decision.units,List.length_nil];omega

def kernelExecution (cache : ReferenceReplayCache I) (data : Kernel I) : Execution I :=
  ⟨some cache,data.calls,data.rationalTests,data.naturalTests,[data.archiveIndex],
    [⟨.cursor,data.cursorVisits⟩],0,data.localTicks⟩

def decisionExecution {input : StatisticalInput I} (cache : ReferenceReplayCache I)
    (result : Decision input) : Execution I :=
  ⟨some cache,[],[],result.naturalTests,[],result.historyReads,result.copied,result.localTicks⟩

structure Computation (input : StatisticalInput I) where
  action : Action I
  work : Execution I
  words : List (WordCall input)

def candidate (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I)) (records : List Nat) : Computation input :=
  let run:=replay input available budget records history
  match run.result with
  | none => ⟨.abandon,{run with localTicks:=run.localTicks+2},[]⟩
  | some cache =>
      let data:=kernel budget records cache
      let result:=decisionBody input limit history cache data
      ⟨result.action,join run (join (kernelExecution cache data) (decisionExecution cache result)),result.words⟩

theorem candidate_result (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I)) (records : List Nat) :
    (candidate input available budget limit history records).action=
      recordCandidatePlanner input available budget limit history records := by
  unfold candidate recordCandidatePlanner
  rw [←replay_result]
  dsimp only
  cases (replay input available budget records history).result with
  | none => rfl
  | some cache => exact decisionBody_result input budget limit history records cache

def Computation.units {input : StatisticalInput I} (result : Computation input) : Nat :=
  result.work.units+result.words.length

theorem kernelExecution_units (budget : Rat) (records : List Nat) (cache : ReferenceReplayCache I) :
    (kernelExecution cache (kernel budget records cache)).units≤30*(cache.events.length+1) := by
  have counts:=kernel_counts budget records cache
  simp only [kernelExecution,Execution.units,List.length_cons,List.length_nil]
  omega

theorem candidate_units (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I)) (records : List Nat) :
    (candidate input available budget limit history records).units≤512*(history.length+1)^2 := by
  have replayCost:=replay_units input available budget records history
  unfold candidate
  dsimp only
  cases finished:(replay input available budget records history).result with
  | none =>
      simp only [Computation.units,Execution.units,List.length_nil] at *
      have positive : 1≤(history.length+1)^2:=Nat.one_le_pow _ _ (by omega)
      omega
  | some cache =>
      have bounded:=replay_cacheBound input available budget records history cache finished
      have data:=kernelExecution_units budget records cache
      have result:=decisionBody_units input limit history cache (kernel budget records cache)
      simp only [Computation.units,join_units]
      have erased : (decisionExecution cache (decisionBody input limit history cache (kernel budget records cache))).units+
          (decisionBody input limit history cache (kernel budget records cache)).words.length=
          (decisionBody input limit history cache (kernel budget records cache)).units := by
        simp only [decisionExecution,Execution.units,Decision.units,List.length_nil]
        omega
      rcases bounded with ⟨seen,entry,events⟩
      nlinarith

theorem actual_native_candidate (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0<budget) (small : budget≤1/2) (limit : ReferenceObservationLimit I)
    (policy : Policy input C .native accounting Unit)
    (sameRule : policy.rule=tableRule input available budget limit)
    (sample : Unit×input.World) (clock : Nat) :
    let state:=run input C .native accounting policy.rule sample clock
    (candidate input available budget limit state.history (nativeRecords available state.history)).action=
      policy.rule () state.history := by
  dsimp only
  rw [candidate_result]
  exact actual_native_record_candidate input C laminar current accounting available budget
    positive small limit policy sameRule sample clock

end RootPaper.TableCost
