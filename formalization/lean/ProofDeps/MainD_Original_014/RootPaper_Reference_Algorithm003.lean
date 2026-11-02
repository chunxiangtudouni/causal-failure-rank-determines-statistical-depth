module
public import RootPaper_Reference_Kernel002

/-! The original reference cache algorithm with shared concrete queries.
This is one controller, not a general-purpose replay interpreter. Each
completed cache step carries the kernel's actual DFS/scalar call record. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
variable {I : Instance}

structure Snapshot (I : Instance) where
  stage : Option I.Stage
  cursor : Nat
  actions : Nat
  used : Finset I.Tool
  written : Option (Bool×Nat)
  reported : Option (Bool×Nat)
  observations : List Nat

def snapshot (cache : ReferenceReplayCache I) : Snapshot I :=
  let cursor:=historyCursor cache.seen
  let actions:=(historyActions cache.seen).length
  let used:=historyUsed cache.seen
  match referenceReplayStage I cache with
  | none => ⟨none,cursor,actions,used,none,none,[]⟩
  | some stage => ⟨some stage,cursor,actions,used,historyWrite cache.seen stage,
      historyReport cache.seen stage,historyObservations cache.seen stage⟩

def Snapshot.mismatch (view : Snapshot I) (handle : MismatchHandle I) : Bool :=
  match view.stage,view.written,view.reported with
  | some stage,some (bit,serial),some (truth,reportedSerial) =>
      decide (bit≠truth ∧ handle.stage=stage ∧ handle.writeSerial=serial ∧ reportedSerial=serial)
  | _,_,_ => false
def Snapshot.correct (view : Snapshot I) : Bool :=
  match view.written,view.reported with
  | some (bit,serial),some (truth,reportedSerial) => decide (bit=truth ∧ reportedSerial=serial)
  | _,_ => false
def Snapshot.handle (view : Snapshot I) : Option (MismatchHandle I) := do
  let stage←view.stage
  let written←view.written
  some ⟨stage,written.2⟩

theorem snapshot_stage (cache : ReferenceReplayCache I) :
    (snapshot cache).stage=referenceReplayStage I cache := by
  unfold snapshot
  cases referenceReplayStage I cache <;> rfl

theorem kernel_repair (available : Finset I.Tool) (budget : Rat) (cache : ReferenceReplayCache I)
    (stage : I.Stage) (current : referenceReplayStage I cache=some stage) :
    (kernel I available budget cache).repair=
      referenceAvailableRepairTool I available stage (historyUsed cache.entryHistory) := by
  simpa only [kernel,current] using kindWork_repair available stage (historyUsed cache.entryHistory)

def stepBody (input : StatisticalInput I) (available : Finset I.Tool)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) (data : Kernel I) : Option (ReferenceReplayCache I) :=
  let view:=snapshot cache
  let recorded:={cache with seen:=cache.seen++[event]}
  if cache.halted then none else
  match event with
  | .observation i symbol => do
      let stage←view.stage
      if i=stage ∧ symbol<(input.experiment i).alphabetSize ∧ cache.phase=.testing ∧ data.target.isSome
        then some recorded else none
  | .wrote i _ serial => do
      let stage←view.stage
      let _kind←data.classification
      let _current←data.current
      if i=stage ∧ serial=view.actions ∧ cache.phase=.testing then some {recorded with phase:=.written} else none
  | .report i truth serial => do
      let stage←view.stage
      let written←view.written
      let kind←data.classification
      let _current←data.current
      if i=stage ∧ serial=written.2 ∧ cache.phase=.written ∧ cache.events.length<I.stageCount
        then some {recorded with events:=cache.events++[(kind,decide (written.1≠truth))],phase:=.reported} else none
  | .committed handle tool => do
      let stage←view.stage
      let _current←data.current
      if cache.phase=.reported ∧ view.mismatch handle ∧ tool∈I.eligible stage ∧ tool∉view.used ∧
          tool∈available ∧ data.repair=some tool then some {recorded with phase:=.allocated tool} else none
  | .executed handle tool => do
      let _stage←view.stage
      if cache.phase=.allocated tool ∧ view.mismatch handle then some {recorded with phase:=.executed tool} else none
  | .advanced i => do
      let stage←view.stage
      let _current←data.current
      if i=stage ∧ ((cache.phase=.reported ∧ view.correct) ∨ ∃ tool,cache.phase=.executed tool)
        then some {recorded with entryHistory:=recorded.seen,phase:=.testing} else none
  | .stopped => if view.cursor=I.stageCount ∧ cache.phase=.testing then some {recorded with halted:=true} else none
  | .abandoned => if cache.phase≠.written then some {recorded with halted:=true} else none

def stepValue (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) : Option (ReferenceReplayCache I) :=
  stepBody input available cache event (kernel I available budget cache)

attribute [local irreducible] kernel
theorem snapshot_some (cache : ReferenceReplayCache I) (stage : I.Stage)
    (current : referenceReplayStage I cache=some stage) :
    snapshot cache=⟨some stage,historyCursor cache.seen,(historyActions cache.seen).length,
      historyUsed cache.seen,historyWrite cache.seen stage,historyReport cache.seen stage,
      historyObservations cache.seen stage⟩ := by simp only [snapshot,current]

theorem snapshot_none (cache : ReferenceReplayCache I) (current : referenceReplayStage I cache=none) :
    snapshot cache=⟨none,historyCursor cache.seen,(historyActions cache.seen).length,
      historyUsed cache.seen,none,none,[]⟩ := by simp only [snapshot,current]

theorem snapshot_mismatch (cache : ReferenceReplayCache I) (stage : I.Stage)
    (current : referenceReplayStage I cache=some stage) :
    (snapshot cache).mismatch=referenceReplayMismatch cache stage := by
  rw [snapshot_some cache stage current]
  funext handle
  unfold Snapshot.mismatch referenceReplayMismatch
  cases historyWrite cache.seen stage <;> cases historyReport cache.seen stage <;> rfl

theorem snapshot_correct (cache : ReferenceReplayCache I) (stage : I.Stage)
    (current : referenceReplayStage I cache=some stage) :
    (snapshot cache).correct=referenceReplayCorrect cache stage := by
  rw [snapshot_some cache stage current]
  rfl

theorem stepValue_eq (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) :
    stepValue input available budget cache event=referenceAvailableStep input available budget cache event := by
  obtain ⟨kindEq,currentEq,targetEq⟩:=kernel_values available budget cache
  unfold stepValue stepBody referenceAvailableStep
  rw [kindEq,currentEq,targetEq]
  cases halted : cache.halted with
  | true => simp only [ite_true]
  | false =>
      simp only [Bool.false_eq_true,ite_false]
      cases current : referenceReplayStage I cache with
      | none => rw [snapshot_none cache current];cases event <;> rfl
      | some stage =>
          have repairEq:=kernel_repair available budget cache stage current
          rw [snapshot_mismatch cache stage current,snapshot_correct cache stage current,repairEq,
            snapshot_some cache stage current]
          cases event <;> rfl

structure Execution (I : Instance) where
  result : Option (ReferenceReplayCache I)
  ranks : List (RankCall I)
  scalar : List (ScalarCall I)
  historyReads : List Nat
  copied : Nat

/-- The fixed scan schedule bounds the source's history helper inputs:
cursor, actions, used, write/report, observations, and entry-used. The
stage-none case may do fewer reads. Copies include seen/event appends. -/
def step (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) : Execution I :=
  let data:=kernel I available budget cache
  ⟨stepBody input available cache event data,data.ranks,data.scalar,
    [cache.seen.length,cache.seen.length,cache.seen.length,cache.seen.length,
     cache.seen.length,cache.seen.length,cache.seen.length,cache.entryHistory.length],
    cache.seen.length+cache.events.length+2⟩

theorem step_result (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) :
    (step input available budget cache event).result=referenceAvailableStep input available budget cache event :=
  stepValue_eq input available budget cache event

def replayFrom (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) : List (VisibleEvent I)→Execution I
  | [] => ⟨some cache,[],[],[],0⟩
  | event::rest =>
      let front:=step input available budget cache event
      match front.result with
      | none => front
      | some next =>
          let tail:=replayFrom input available budget next rest
          ⟨tail.result,front.ranks++tail.ranks,front.scalar++tail.scalar,
            front.historyReads++tail.historyReads,front.copied+tail.copied⟩

theorem replayFrom_eq (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (history : List (VisibleEvent I)) :
    (replayFrom input available budget cache history).result=
      history.foldlM (referenceAvailableStep input available budget) cache := by
  induction history generalizing cache with
  | nil => rfl
  | cons event rest ih =>
      simp only [replayFrom,step_result,List.foldlM_cons]
      cases actual : referenceAvailableStep input available budget cache event with
      | none =>
          change (step input available budget cache event).result=none
          exact (step_result input available budget cache event).trans actual
      | some next =>
          change (replayFrom input available budget next rest).result=rest.foldlM (referenceAvailableStep input available budget) next
          exact ih next

end RootPaper.Reference
