module
public import RootPaper_Reference_Rank001
public import PaperProofs.Common.ReferenceController

/-! A specific eager cache kernel for the original reference algorithm.
Only the original rank, budget fold, and target are computed. Records contain
actual operands and measured DFS transitions; there is no general interpreter. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RationalControllerComputation
variable {I : Instance}

inductive ScalarCall (I : Instance) where
  | budgetVisit (kind : ReferenceBudgetCase) (error : Bool) (risk : Rat)
  | half (risk : Rat)
  | target (risk : Rat) (depth : Nat)
  | badRisk (risk target : Rat)
  | word (stage : I.Stage) (target : Rat) (length : Nat)

def targetWork (kind : ReferenceBudgetCase) (risk : Rat) : Option Rat×List (ScalarCall I) :=
  match kind with
  | .infiniteRank => (none,[])
  | .noTool => (some (risk/2),[.half risk])
  | .finiteBad depth => (some (controllerTarget risk depth.val),[.target risk depth.val])

theorem targetWork_value (kind : ReferenceBudgetCase) (risk : Rat) :
    (targetWork (I:=I) kind risk).1=referenceBudgetTarget kind risk := by cases kind <;> rfl
theorem targetWork_calls (kind : ReferenceBudgetCase) (risk : Rat) :
    (targetWork (I:=I) kind risk).2.length≤1 := by cases kind <;> simp [targetWork]

def budgetArithmetic (kind : ReferenceBudgetCase) (error : Bool) (risk : Rat) : Option Rat×List (ScalarCall I) :=
  match kind with
  | .infiniteRank => (some risk,[])
  | .noTool => if error then (none,[]) else (some (risk/2),[.half risk])
  | .finiteBad depth => if error then
      let target:=controllerTarget risk depth.val
      (some (controllerBadRisk risk target),[.target risk depth.val,.badRisk risk target])
    else (some (risk/2),[.half risk])
def budgetStepWork (kind : ReferenceBudgetCase) (error : Bool) (risk : Rat) : Option Rat×List (ScalarCall I) :=
  let result:=budgetArithmetic kind error risk
  (result.1,.budgetVisit kind error risk::result.2)
theorem budgetStepWork_value (kind : ReferenceBudgetCase) (error : Bool) (risk : Rat) :
    (budgetStepWork (I:=I) kind error risk).1=referenceBudgetStep kind error risk := by
  cases kind <;> cases error <;> rfl
theorem budgetStepWork_calls (kind : ReferenceBudgetCase) (error : Bool) (risk : Rat) :
    (budgetStepWork (I:=I) kind error risk).2.length≤3 := by
  cases kind <;> cases error <;> simp [budgetStepWork,budgetArithmetic]

def budgetWork (initial : Rat) : List ReferenceBudgetEvent→Option Rat×List (ScalarCall I)
  | [] => (some initial,[])
  | event::rest =>
      let step:=budgetStepWork event.1 event.2 initial
      match step.1 with
      | none => (none,step.2)
      | some child =>
          let tail:=budgetWork child rest
          (tail.1,step.2++tail.2)

theorem budgetWork_value (initial : Rat) (events : List ReferenceBudgetEvent) :
    (budgetWork (I:=I) initial events).1=referenceBudgetPath initial events := by
  induction events generalizing initial with
  | nil => rfl
  | cons event rest ih =>
      simp only [budgetWork,referenceBudgetPath,←budgetStepWork_value (I:=I)]
      cases (budgetStepWork (I:=I) event.1 event.2 initial).1 <;> simp only [Option.bind_none,Option.bind_some,ih]

theorem budgetWork_calls (initial : Rat) (events : List ReferenceBudgetEvent) :
    (budgetWork (I:=I) initial events).2.length≤3*events.length := by
  induction events generalizing initial with
  | nil => simp [budgetWork]
  | cons event rest ih =>
      have step:=budgetStepWork_calls (I:=I) event.1 event.2 initial
      simp only [budgetWork]
      cases choice : (budgetStepWork (I:=I) event.1 event.2 initial).1 with
      | none => simpa only [List.length_cons] using step.trans (by omega)
      | some child =>
          have tail:=ih child
          simp only [List.length_append,List.length_cons]
          omega

structure RankCall (I : Instance) where
  stage : Nat
  remaining : Finset I.Tool
  transitions : Nat

structure KindWork (I : Instance) where
  classification : Option ReferenceBudgetCase
  repair : Option I.Tool
  ranks : List (RankCall I)

def kindWork (I : Instance) (available : Finset I.Tool) (stage : I.Stage) (used : Finset I.Tool) : KindWork I :=
  let remaining:=available\used
  let root:=query I stage.val remaining
  let call : RankCall I:=⟨stage.val,remaining,root.transitions⟩
  match root.pick with
  | none => ⟨referenceCaseOfRanks root.rank 0,none,[call]⟩
  | some tool =>
      let child:=query I (stage.val+1) (remaining.erase tool)
      ⟨referenceCaseOfRanks root.rank child.rank,some tool,
        [call,⟨stage.val+1,remaining.erase tool,child.transitions⟩]⟩

theorem kindWork_value (available : Finset I.Tool) (stage : I.Stage) (used : Finset I.Tool) :
    (kindWork I available stage used).classification=referenceAvailableRankCase I available stage used := by
  rw [←kind_eq]
  dsimp only [kindWork,kind]
  cases (query I stage.val (available\used)).pick <;> rfl

theorem kindWork_repair (available : Finset I.Tool) (stage : I.Stage) (used : Finset I.Tool) :
    (kindWork I available stage used).repair=referenceAvailableRepairTool I available stage used := by
  have same : (kindWork I available stage used).repair=(query I stage.val (available\used)).pick := by
    dsimp only [kindWork]
    cases (query I stage.val (available\used)).pick <;> rfl
  rw [same,query_pick]
  unfold referenceAvailableRepairTool referenceRepairTool
  rw [referenceRank_remaining]

theorem kindWork_calls (available : Finset I.Tool) (stage : I.Stage) (used : Finset I.Tool) :
    (kindWork I available stage used).ranks.length≤2 ∧
    ((kindWork I available stage used).ranks.map RankCall.transitions).sum≤6*generalStructureFactor I := by
  have root:=(query_spec I stage.val (available\used)).2.2
  dsimp only [kindWork]
  cases picked : (query I stage.val (available\used)).pick with
  | none => simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil];omega
  | some tool =>
      have child:=(query_spec I (stage.val+1) ((available\used).erase tool)).2.2
      simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      omega

structure Kernel (I : Instance) where
  classification : Option ReferenceBudgetCase
  repair : Option I.Tool
  current : Option Rat
  target : Option Rat
  ranks : List (RankCall I)
  scalar : List (ScalarCall I)

def kernel (I : Instance) (available : Finset I.Tool) (budget : Rat) (cache : ReferenceReplayCache I) : Kernel I :=
  let current:=budgetWork (I:=I) (budget/2) cache.events
  match referenceReplayStage I cache with
  | none => ⟨none,none,current.1,none,[],.half budget::current.2⟩
  | some stage =>
      let rank:=kindWork I available stage (historyUsed cache.entryHistory)
      let target : Option Rat×List (ScalarCall I):=
        if cache.halted || decide (cache.phase≠.testing) then (none,[]) else
          match rank.classification,current.1 with
          | some kind,some risk => if 0<risk ∧ risk≤1/4 ∧ cache.events.length≤I.stageCount
              then targetWork kind risk else (none,[])
          | _,_ => (none,[])
      ⟨rank.classification,rank.repair,current.1,target.1,rank.ranks,.half budget::current.2++target.2⟩

private theorem no_pair_bind {α β γ : Type*} (left : Option α) (right : Option β)
    (value : α→β→Option γ)
    (absent : ∀ a b, left = some a → right ≠ some b) :
    (left.bind (fun a => right.bind (value a)))=none := by
  cases left <;> cases right <;> simp_all

attribute [local simp] targetWork_value
theorem kernel_values (available : Finset I.Tool) (budget : Rat) (cache : ReferenceReplayCache I) :
    (kernel I available budget cache).classification=referenceAvailableKind I available cache ∧
    (kernel I available budget cache).current=referenceReplayRisk budget cache ∧
    (kernel I available budget cache).target=referenceAvailableCacheTarget I available budget cache := by
  simp only [kernel,referenceAvailableKind,referenceReplayRisk,referenceAvailableCacheTarget,
    budgetWork_value,kindWork_value]
  all_goals repeat' split
  all_goals simp_all
  all_goals exact (no_pair_bind _ _ _ (by assumption)).symm

end RootPaper.Reference
