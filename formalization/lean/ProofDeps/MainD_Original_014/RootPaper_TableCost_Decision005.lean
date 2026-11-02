module

public import RootPaper_TableCost_Replay004

/-! The TABLE candidate's concrete action computation. The WORD operand is
the validated word itself, including the zero-length word. A failed hit
retains its WORD call before inspecting a quota; no quota shortcut is used. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootPaper.TableCost

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open CompactPrice PSTRTableRecordPlanner PSTRTML01CacheRecord252

variable {I : Instance}

structure WordCall (input : StatisticalInput I) where
  stage : I.Stage
  target : Rat
  word : (input.experiment stage).StoppedWord

structure Decision (input : StatisticalInput I) where
  action : Action I
  words : List (WordCall input)
  naturalTests : List (Nat×Nat)
  historyReads : List HistoryRead
  copied : Nat
  localTicks : Nat

def bare (input : StatisticalInput I) (action : Action I) (ticks : Nat) : Decision input :=
  ⟨action,[],[],[],5,ticks⟩

def testing (input : StatisticalInput I) (limit : ReferenceObservationLimit I)
    (cache : ReferenceReplayCache I) (data : Kernel I) (stage : I.Stage) : Decision input :=
  match data.kind with
  | none => bare input .abandon 2
  | some .infiniteRank => bare input (.write stage false) 4
  | some .noTool | some (.finiteBad _) =>
    match data.target with
    | none => bare input .abandon 4
    | some target =>
      let observations:=historyObservations cache.seen stage
      let tests:=observations.map (fun symbol => (symbol,(input.experiment stage).alphabetSize))
      let reads:=[HistoryRead.mk .observations cache.seen.length,
        HistoryRead.mk .experiment (instanceMaterial input+I.stageCount)]
      if valid:∀ symbol∈historyObservations cache.seen stage,symbol<(input.experiment stage).alphabetSize then
        let word:=historyObservationWord input cache.seen stage valid
        let answer:=((input.experiment stage).rationalWordHits target word,
          (input.experiment stage).rationalWordMAP word)
        let call:WordCall input:=⟨stage,target,word⟩
        if answer.1 then ⟨.write stage answer.2,[call],tests,reads,observations.length+5,24⟩ else
          match limit with
          | none => ⟨.review stage,[call],tests,reads,observations.length+5,24⟩
          | some quota =>
            ⟨if observations.length<quota stage then .review stage else .abandon,
              [call],tests++[(observations.length,quota stage)],reads,observations.length+5,28⟩
      else ⟨.abandon,[],tests,reads,observations.length+5,20⟩

def decisionBody (input : StatisticalInput I) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I) (data : Kernel I) : Decision input :=
  if cache.halted then bare input .stop 2 else
  match stageAt data with
  | none =>
      ⟨if historyCursor history=I.stageCount then .stop else .abandon,[],
        [(historyCursor history,I.stageCount)],[⟨.cursor,history.length⟩],5,8⟩
  | some stage =>
      match cache.phase with
      | .testing => testing input limit cache data stage
      | .written => bare input .abandon 2
      | .reported =>
          if referenceReplayCorrect cache stage then
            ⟨.advance stage,[],[],[⟨.correct,cache.seen.length⟩],5,8⟩
          else
            let handle:=referenceVisibleHandle history stage
            let action:=match data.current,handle,data.tool with
              | some _,some handle,some tool => .allocate handle tool
              | _,_,_ => .abandon
            ⟨action,[],[],[⟨.correct,cache.seen.length⟩,⟨.handle,history.length⟩],5,16⟩
      | .allocated tool =>
          let action:=match referenceVisibleHandle history stage with
            | none => .abandon
            | some handle => .execute handle tool
          ⟨action,[],[],[⟨.handle,history.length⟩],5,8⟩
      | .executed _ => bare input (.advance stage) 4

theorem testing_result (input : StatisticalInput I) (budget : Rat) (limit : ReferenceObservationLimit I)
    (records : List Nat) (cache : ReferenceReplayCache I) (stage : I.Stage) :
    (testing input limit cache (kernel budget records cache) stage).action=
      recordTestingAction input budget limit records cache stage := by
  obtain ⟨kindEq,toolEq,currentEq,targetEq⟩:=kernel_values budget records cache
  unfold testing recordTestingAction
  simp only [kindEq,targetEq]
  cases recordKindAtCache records cache with
  | none => rfl
  | some kind =>
      cases kind with
      | infiniteRank => rfl
      | noTool | finiteBad depth =>
          cases recordTarget budget records cache with
          | none => rfl
          | some target =>
              dsimp only
              split_ifs
              all_goals cases limit <;> rfl

theorem decisionBody_result (input : StatisticalInput I) (budget : Rat) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) (records : List Nat) (cache : ReferenceReplayCache I) :
    (decisionBody input limit history cache (kernel budget records cache)).action=
      recordCandidateFromCache input budget limit history records cache := by
  obtain ⟨kindEq,toolEq,currentEq,targetEq⟩:=kernel_values budget records cache
  unfold decisionBody recordCandidateFromCache
  simp only [kernel_stage,currentEq,toolEq]
  cases halted:cache.halted with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true,ite_false]
      cases referenceReplayStage I cache with
      | none => split_ifs <;> rfl
      | some stage =>
          dsimp only
          cases cache.phase with
          | testing => exact testing_result input budget limit records cache stage
          | written => rfl
          | reported =>
              dsimp only
              split_ifs
              · rfl
              · cases referenceReplayRisk budget cache <;>
                  cases referenceVisibleHandle history stage <;>
                    cases recordToolAtCache records cache <;> rfl
          | allocated tool => cases referenceVisibleHandle history stage <;> rfl
          | executed tool => rfl

def Decision.units {input : StatisticalInput I} (result : Decision input) : Nat :=
  result.words.length+result.naturalTests.length+result.historyReads.length+result.copied+result.localTicks

end RootPaper.TableCost
