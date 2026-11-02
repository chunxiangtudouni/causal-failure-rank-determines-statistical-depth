module

public import RootPaper_TableCost_Archive001
public import RootPaper_Reference_Kernel002
public import Common.PSTR_L01_NativeRecordCandidate_011

/-! TABLE-only annotated scalar kernel. Kind and tool come from ONE saved
four-word packet. The actual budget recursion is the frozen shared kernel;
no generic kindWork/query/DFS is called. Value and operation operands are
returned together, on the same branches as the target computation. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootPaper.TableCost

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open PaperProofs.Structure PaperProofs.Structure.LaminarTree
open CompactPrice PSTRTableRecordDecision PSTRTablePlannerStreams
open PSTRTML01CacheRecord252 PSTRTML01RecordReplay253 PSTRTableRecordPlanner

variable {I : Instance}

structure TargetWork (I : Instance) where
  value : Option Rat
  calls : List (RootPaper.Reference.ScalarCall I)
  rationalTests : List (Rat×Rat)
  naturalTests : List (Nat×Nat)
  localTicks : Nat

def targetAt (kind : Option ReferenceBudgetCase) (current : Option Rat)
    (cache : ReferenceReplayCache I) : TargetWork I :=
  if cache.halted || decide (cache.phase≠.testing) then ⟨none,[],[],[],2⟩ else
  match kind,current with
  | some kind,some risk =>
      let positive:=0<risk
      let small:=risk≤1/4
      let reports:=cache.events.length≤I.stageCount
      let result:=if positive ∧ small ∧ reports then RootPaper.Reference.targetWork (I:=I) kind risk else (none,[])
      ⟨result.1,result.2,[(risk,0),(risk,1/4)],[(cache.events.length,I.stageCount)],8⟩
  | _,_ => ⟨none,[],[],[],4⟩

theorem targetAt_value (kind : Option ReferenceBudgetCase) (current : Option Rat)
    (cache : ReferenceReplayCache I) :
    (targetAt kind current cache).value=
      (if cache.halted || decide (cache.phase≠.testing) then none else do
        let classification←kind
        let risk←current
        if 0<risk ∧ risk≤1/4 ∧ cache.events.length≤I.stageCount then
          referenceBudgetTarget classification risk else none) := by
  by_cases stopped:(cache.halted || decide (cache.phase≠.testing))=true
  · simp only [targetAt,stopped,ite_true]
  · simp only [targetAt,stopped]
    cases kind with
    | none => rfl
    | some kind =>
        cases current with
        | none => rfl
        | some risk =>
            simp only [Option.bind_eq_bind,Option.bind_some]
            split_ifs <;> simp only [RootPaper.Reference.targetWork_value]

theorem targetAt_counts (kind : Option ReferenceBudgetCase) (current : Option Rat)
    (cache : ReferenceReplayCache I) :
    (targetAt kind current cache).calls.length≤1 ∧
    (targetAt kind current cache).rationalTests.length≤2 ∧
    (targetAt kind current cache).naturalTests.length≤1 ∧
    (targetAt kind current cache).localTicks≤8 := by
  unfold targetAt
  split
  · simp
  ·
    cases kind with
    | none => cases current <;> simp
    | some kind =>
        cases current with
        | none => simp
        | some risk =>
            change (if 0<risk ∧ risk≤1/4 ∧ cache.events.length≤I.stageCount then
                RootPaper.Reference.targetWork (I:=I) kind risk else (none,[])).2.length≤1 ∧ 2≤2 ∧ 1≤1 ∧ 8≤8
            refine ⟨?_,by omega,by omega,by omega⟩
            split_ifs
            · exact RootPaper.Reference.targetWork_calls _ _
            · exact Nat.zero_le _

structure Kernel (I : Instance) where
  kind : Option ReferenceBudgetCase
  tool : Option I.Tool
  current : Option Rat
  target : Option Rat
  calls : List (RootPaper.Reference.ScalarCall I)
  rationalTests : List (Rat×Rat)
  naturalTests : List (Nat×Nat)
  archiveIndex : Nat
  cursorVisits : Nat
  localTicks : Nat

/-- The packet is an actual saved archive read; both decoders share it.
The current risk and target are produced with their charged call records. -/
def kernel (budget : Rat) (records : List Nat) (cache : ReferenceReplayCache I) : Kernel I :=
  let index:=historyCursor cache.seen
  let packet:=readRecord records index
  let kind:=recordKind I.toolCount packet
  let tool:=recordTool I.toolCount packet
  let current:=RootPaper.Reference.budgetWork (I:=I) (budget/2) cache.events
  let target:=targetAt kind current.1 cache
  ⟨kind,tool,current.1,target.value,
    .half budget::current.2++target.calls,target.rationalTests,target.naturalTests,
    index,cache.seen.length,target.localTicks+12⟩

theorem kernel_values (budget : Rat) (records : List Nat) (cache : ReferenceReplayCache I) :
    (kernel budget records cache).kind=recordKindAtCache records cache ∧
    (kernel budget records cache).tool=recordToolAtCache records cache ∧
    (kernel budget records cache).current=referenceReplayRisk budget cache ∧
    (kernel budget records cache).target=recordTarget budget records cache := by
  refine ⟨rfl,rfl,RootPaper.Reference.budgetWork_value _ _,?_⟩
  have target:=targetAt_value (I:=I) (recordKindAtCache records cache)
    (RootPaper.Reference.budgetWork (I:=I) (budget/2) cache.events).1 cache
  change (targetAt (recordKindAtCache records cache)
    (RootPaper.Reference.budgetWork (I:=I) (budget/2) cache.events).1 cache).value=_
  rw [target]
  simp only [RootPaper.Reference.budgetWork_value,referenceReplayRisk,recordTarget]

theorem kernel_counts (budget : Rat) (records : List Nat) (cache : ReferenceReplayCache I) :
    (kernel budget records cache).calls.length≤3*cache.events.length+2 ∧
    (kernel budget records cache).rationalTests.length≤2 ∧
    (kernel budget records cache).naturalTests.length≤1 ∧
    (kernel budget records cache).localTicks≤20 := by
  have current:=RootPaper.Reference.budgetWork_calls (I:=I) (budget/2) cache.events
  have target:=targetAt_counts (I:=I) (recordKindAtCache records cache)
    (RootPaper.Reference.budgetWork (I:=I) (budget/2) cache.events).1 cache
  change (.half budget::(RootPaper.Reference.budgetWork (I:=I) (budget/2) cache.events).2++
      (targetAt (recordKindAtCache records cache) _ cache).calls).length≤_ ∧
    (targetAt (recordKindAtCache records cache) _ cache).rationalTests.length≤2 ∧
    (targetAt (recordKindAtCache records cache) _ cache).naturalTests.length≤1 ∧
    (targetAt (recordKindAtCache records cache) _ cache).localTicks+12≤20
  simp only [List.length_cons,List.length_append]
  exact ⟨by omega,target.2.1,target.2.2.1,by omega⟩

end RootPaper.TableCost
