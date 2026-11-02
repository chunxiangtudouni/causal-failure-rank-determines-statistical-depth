module

public import RootPaper_TableCost_Kernel002

/-! The original TABLE step with a charged, eager helper schedule. The
same event branch returns its value, archive/scalar operands, history
navigation and record-copy bookkeeping. Guards may fail after this eager
work; their costs are retained. No rank/eligibility query is performed. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootPaper.TableCost

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open CompactPrice PSTRTML01RecordReplay253 PSTRTML01CacheRecord252

variable {I : Instance}

inductive HistoryHelper where
  | actions | written | reported | mismatch | used | correct | cursor | available
  | experiment | observations | handle | sameHistory | events
  deriving DecidableEq

structure HistoryRead where
  helper : HistoryHelper
  length : Nat

/-- filterMap plus getLast are paid twice; `used` additionally pays
naive duplicate checking. This fixed list implementation needs no DS. -/
def HistoryRead.visits (read : HistoryRead) : Nat :=
  match read.helper with
  | .cursor | .actions | .available | .experiment | .sameHistory | .events => read.length+1
  | .written | .reported | .handle => 2*(read.length+1)
  | .mismatch | .correct => 4*(read.length+1)+8
  | .used | .observations => 4*(read.length+1)^2

def instanceMaterial (input : StatisticalInput I) : Nat :=
  ((RationalControllerComputation.rawInstance input).flatMap RationalControllerComputation.encodeDatum).length

def stageAt (data : Kernel I) : Option I.Stage :=
  if inside:data.archiveIndex<I.stageCount then some ⟨data.archiveIndex,inside⟩ else none

theorem kernel_stage (budget : Rat) (records : List Nat) (cache : ReferenceReplayCache I) :
    stageAt (kernel budget records cache)=referenceReplayStage I cache := rfl

structure Body (I : Instance) where
  result : Option (ReferenceReplayCache I)
  historyReads : List HistoryRead
  naturalTests : List (Nat×Nat)
  copied : Nat
  localTicks : Nat

def body (input : StatisticalInput I) (available : Finset I.Tool)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) (data : Kernel I) : Body I :=
  if cache.halted then ⟨none,[],[],0,2⟩ else
  let recorded:={cache with seen:=cache.seen++[event]}
  let H:=cache.seen.length
  match event with
  | .observation i symbol =>
      let result:=do
        let stage←stageAt data
        if i=stage ∧ symbol<(input.experiment i).alphabetSize ∧ cache.phase=.testing ∧ data.target.isSome
          then some recorded else none
      let tests:=match stageAt data with
        | none => []
        | some stage => [(i.val,stage.val),(symbol,(input.experiment i).alphabetSize)]
      ⟨result,[⟨.experiment,instanceMaterial input⟩],tests,H+1,12⟩
  | .wrote i _ serial =>
      let actions:=(historyActions cache.seen).length
      let result:=do
        let stage←stageAt data
        let _kind←data.kind
        let _current←data.current
        if i=stage ∧ serial=actions ∧ cache.phase=.testing then some {recorded with phase:=.written} else none
      let tests:=match stageAt data with
        | none => [(serial,actions)]
        | some stage => [(i.val,stage.val),(serial,actions)]
      ⟨result,[⟨.actions,H⟩],tests,H+1,14⟩
  | .report i truth serial =>
      let result:=do
        let stage←stageAt data
        let written←historyWrite cache.seen stage
        let kind←data.kind
        let _current←data.current
        if i=stage ∧ serial=written.2 ∧ cache.phase=.written ∧ cache.events.length<I.stageCount
          then some {recorded with events:=cache.events++[(kind,decide (written.1≠truth))],phase:=.reported}
          else none
      let tests:=match stageAt data with
        | none => []
        | some stage => [(i.val,stage.val),(serial,((historyWrite cache.seen stage).map Prod.snd).getD 0),
            (cache.events.length,I.stageCount)]
      ⟨result,[⟨.written,H⟩,⟨.written,H⟩],tests,H+cache.events.length+2,20⟩
  | .committed handle tool =>
      let result:=do
        let stage←stageAt data
        let _current←data.current
        if cache.phase=.reported ∧ referenceReplayMismatch cache stage handle ∧
            tool∉historyUsed cache.seen ∧ tool∈available ∧ data.tool=some tool then
          some {recorded with phase:=.allocated tool} else none
      ⟨result,[⟨.mismatch,H⟩,⟨.used,H⟩,⟨.available,I.toolCount⟩],[(tool.val,I.toolCount)],H+1,24⟩
  | .executed handle tool =>
      let result:=do
        let stage←stageAt data
        if cache.phase=.allocated tool ∧ referenceReplayMismatch cache stage handle then
          some {recorded with phase:=.executed tool} else none
      ⟨result,[⟨.mismatch,H⟩],[(tool.val,I.toolCount)],H+1,16⟩
  | .advanced i =>
      let result:=do
        let stage←stageAt data
        let _current←data.current
        if i=stage ∧ ((cache.phase=.reported ∧ referenceReplayCorrect cache stage) ∨
            ∃ tool,cache.phase=.executed tool) then
          some {recorded with entryHistory:=recorded.seen,phase:=.testing} else none
      let tests:=match stageAt data with | none => [] | some stage => [(i.val,stage.val)]
      ⟨result,[⟨.correct,H⟩],tests,2*(H+1),20⟩
  | .stopped =>
      ⟨if data.archiveIndex=I.stageCount ∧ cache.phase=.testing then some {recorded with halted:=true} else none,
        [],[(data.archiveIndex,I.stageCount)],H+1,8⟩
  | .abandoned =>
      ⟨if cache.phase≠.written then some {recorded with halted:=true} else none,[],[],H+1,6⟩

structure Execution (I : Instance) where
  result : Option (ReferenceReplayCache I)
  calls : List (RootPaper.Reference.ScalarCall I)
  rationalTests : List (Rat×Rat)
  naturalTests : List (Nat×Nat)
  archiveReads : List Nat
  historyReads : List HistoryRead
  copied : Nat
  localTicks : Nat

/-- Source helper access schedule is attached to the very result-producing
kernel/body. Extra eager reads on failed guards are charged, not erased
from the cost. The cursor scan supplies the archive index and stage. -/
def step (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat) (records : List Nat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) : Execution I :=
  let data:=kernel budget records cache
  let next:=body input available cache event data
  ⟨next.result,data.calls,data.rationalTests,data.naturalTests++next.naturalTests,
    [data.archiveIndex],⟨.cursor,data.cursorVisits⟩::next.historyReads,next.copied,data.localTicks+next.localTicks⟩

theorem step_result (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat) (records : List Nat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) :
    (step input available budget records cache event).result=recordStep input available budget records cache event := by
  obtain ⟨kindEq,toolEq,currentEq,targetEq⟩:=kernel_values budget records cache
  have targetEq':(kernel budget records cache).target=targetFromRecords budget records cache:=targetEq
  unfold step body recordStep
  simp only [kindEq,toolEq,currentEq,targetEq',kernel_stage]
  cases halted:cache.halted with
  | true => simp only [ite_true]
  | false =>
      simp only [Bool.false_eq_true,ite_false]
      cases event <;> rfl

theorem body_counts (input : StatisticalInput I) (available : Finset I.Tool)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) (data : Kernel I) :
    (body input available cache event data).historyReads.length≤3 ∧
    (body input available cache event data).naturalTests.length≤3 ∧
    (body input available cache event data).localTicks≤24 ∧
    (body input available cache event data).copied≤2*(cache.seen.length+cache.events.length+1) := by
  unfold body
  split
  · simp
  · cases event
    all_goals dsimp only
    all_goals simp only [List.length_cons,List.length_nil]
    all_goals try (cases stageAt data <;> simp only [List.length_cons,List.length_nil] <;> omega)
    all_goals omega

end RootPaper.TableCost
