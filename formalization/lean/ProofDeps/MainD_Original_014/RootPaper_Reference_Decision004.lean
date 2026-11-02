module
public import RootPaper_Reference_Algorithm003
public import PaperProofs.Common.ReferenceControllerPreservation

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
variable {I : Instance}

def testingWork (input : StatisticalInput I) (quota : I.Stage→Nat)
    (cache : ReferenceReplayCache I) (stage : I.Stage) (data : Kernel I) : Action I×List (ScalarCall I) :=
  match data.classification with
  | none => (.abandon,[])
  | some .infiniteRank => (.write stage false,[])
  | some .noTool | some (.finiteBad _) =>
      match data.target with
      | none => (.abandon,[])
      | some target =>
          if valid : ∀ symbol∈historyObservations cache.seen stage,symbol<(input.experiment stage).alphabetSize then
            let word:=historyObservationWord input cache.seen stage valid
            let odds:=(input.experiment stage).rationalWordOdds word
            let hit:=decide (odds≤target/(1-target) ∨ (1-target)/target≤odds)
            let choice:=decide (1≤odds)
            (if hit then .write stage choice else
              if word.1<quota stage then .review stage else .abandon,
             [.word stage target word.1])
          else (.abandon,[])

theorem testingWork_value (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (quota : I.Stage→Nat) (cache : ReferenceReplayCache I) (stage : I.Stage) :
    (testingWork input quota cache stage (kernel I available budget cache)).1=
      referenceTestingAction input available budget (some quota) cache stage := by
  obtain ⟨kindEq,_currentEq,targetEq⟩:=kernel_values available budget cache
  simp only [testingWork,referenceTestingAction,kindEq,targetEq]
  cases referenceAvailableKind I available cache with
  | none => rfl
  | some kind =>
      cases kind with
      | infiniteRank => rfl
      | noTool | finiteBad depth =>
          cases referenceAvailableCacheTarget I available budget cache with
          | none => rfl
          | some target =>
              dsimp only
              by_cases valid : ∀ symbol∈historyObservations cache.seen stage,
                  symbol<(input.experiment stage).alphabetSize
              · simp only [dite_eq_left valid]
                rfl
              · simp only [dite_eq_right valid]

def cacheAction (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (quota : I.Stage→Nat) (cache : ReferenceReplayCache I) : Action I :=
  if cache.halted then .stop else
  match referenceReplayStage I cache with
  | none => if historyCursor cache.seen=I.stageCount then .stop else .abandon
  | some stage =>
      match cache.phase with
      | .testing => referenceTestingAction input available budget (some quota) cache stage
      | .written => .abandon
      | .reported => if referenceReplayCorrect cache stage then .advance stage else
          match referenceReplayRisk budget cache,referenceVisibleHandle cache.seen stage,
              referenceAvailableRepairTool I available stage (historyUsed cache.entryHistory) with
          | some _,some handle,some tool => .allocate handle tool
          | _,_,_ => .abandon
      | .allocated tool => match referenceVisibleHandle cache.seen stage with
          | none => .abandon | some handle => .execute handle tool
      | .executed _ => .advance stage

def decisionBody (input : StatisticalInput I) (quota : I.Stage→Nat)
    (cache : ReferenceReplayCache I) (data : Kernel I) : Action I×List (ScalarCall I) :=
  if cache.halted then (.stop,[]) else
  match referenceReplayStage I cache with
  | none => (if historyCursor cache.seen=I.stageCount then .stop else .abandon,[])
  | some stage =>
      match cache.phase with
      | .testing => testingWork input quota cache stage data
      | .written => (.abandon,[])
      | .reported => if referenceReplayCorrect cache stage then (.advance stage,[]) else
          match data.current,referenceVisibleHandle cache.seen stage,data.repair with
          | some _,some handle,some tool => (.allocate handle tool,[])
          | _,_,_ => (.abandon,[])
      | .allocated tool => match referenceVisibleHandle cache.seen stage with
          | none => (.abandon,[]) | some handle => (.execute handle tool,[])
      | .executed _ => (.advance stage,[])

theorem decisionBody_value (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (quota : I.Stage→Nat) (cache : ReferenceReplayCache I) :
    (decisionBody input quota cache (kernel I available budget cache)).1=cacheAction input available budget quota cache := by
  obtain ⟨_kindEq,currentEq,_targetEq⟩:=kernel_values available budget cache
  cases halted : cache.halted with
  | true => simp only [decisionBody,cacheAction,halted,ite_true]
  | false =>
    simp only [decisionBody,cacheAction,halted,Bool.false_eq_true,ite_false]
    cases current : referenceReplayStage I cache with
    | none => rfl
    | some stage =>
        simp only
        cases cache.phase with
        | testing => exact testingWork_value input available budget quota cache stage
        | written => rfl
        | reported =>
            dsimp only
            rw [currentEq,kernel_repair available budget cache stage current]
            cases correct : referenceReplayCorrect cache stage with
            | true => simp only [ite_true]
            | false =>
                simp only [Bool.false_eq_true,ite_false]
                cases referenceReplayRisk budget cache <;>
                  cases referenceVisibleHandle cache.seen stage <;>
                  cases referenceAvailableRepairTool I available stage (historyUsed cache.entryHistory) <;> rfl
        | allocated tool => cases referenceVisibleHandle cache.seen stage <;> rfl
        | executed tool => rfl

def replay (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (history : List (VisibleEvent I)) : Execution I :=
  let run:=replayFrom input available budget (referenceReplayInitial I) history
  let result:=do
    if 0<budget ∧ budget≤1/2 then pure () else none
    let cache←run.result
    if cache.phase≠.written ∧ cache.events.length≤I.stageCount ∧
        historyCursor cache.seen≤I.stageCount ∧ cache.seen=history then some cache else none
  {run with result:=result}

theorem replay_value (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (history : List (VisibleEvent I)) :
    (replay input available budget history).result=referenceAvailableReplay input available budget history := by
  simp only [replay,replayFrom_eq,referenceAvailableReplay]

structure Decision (I : Instance) where
  action : Action I
  ranks : List (RankCall I)
  scalar : List (ScalarCall I)
  historyReads : List Nat
  copied : Nat

def controller (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (quota : I.Stage→Nat) (history : List (VisibleEvent I)) : Decision I :=
  let replayed:=replay input available budget history
  match replayed.result with
  | none => ⟨.abandon,replayed.ranks,replayed.scalar,replayed.historyReads,replayed.copied⟩
  | some cache =>
      let data:=kernel I available budget cache
      let decision:=decisionBody input quota cache data
      ⟨decision.1,replayed.ranks++data.ranks,replayed.scalar++data.scalar++decision.2,
        replayed.historyReads++List.replicate 16 cache.seen.length,
        replayed.copied+cache.seen.length+cache.events.length+1⟩

theorem controller_candidate (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (quota : I.Stage→Nat) (history : List (VisibleEvent I)) :
    (controller input available budget quota history).action=
      referenceCandidateAction input available budget (some quota) history := by
  simp only [controller,replay_value,decisionBody_value]
  cases parsed : referenceAvailableReplay input available budget history with
  | none => simp only [referenceCandidateAction,parsed]
  | some cache =>
      have seen:=(referenceAvailableReplay_some_spec input available budget history cache parsed).2.2.2.2.2
      simp only [referenceCandidateAction,parsed]
      rw [←seen]
      rfl

theorem same_rule_of_prefix {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (early : C.reporting=.early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : Rat) (positive : 0<budget) (small : budget≤1/2) (quota : I.Stage→Nat)
    (seed : Seed) (truth : I.Stage→Bool) (tapes : ReviewTapes input) {n : Nat} {state : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget (some quota)) seed truth tapes n state) :
    (controller input available budget quota state.history).action=
      referenceRule input available budget (some quota) seed state.history := by
  exact (controller_candidate input available budget quota state.history).trans
    (referenceRule_eq_candidate_of_prefix input C early accounting available budget positive small (some quota)
      seed truth tapes hp).symm

end RootPaper.Reference
