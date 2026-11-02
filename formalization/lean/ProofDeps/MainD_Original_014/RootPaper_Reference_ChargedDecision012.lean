module
public import RootPaper_Reference_ChargedBody011
public import RootPaper_Reference_Decision004

/-! The decision consumes its measured snapshot, validated observations and
measured word length. WORD is recorded with its complete original input.
The quota getter returns its actual linked-record visits along with Q. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RootPaper.Reference
variable {I : Instance}

def wordAtLength (E : BinaryExperiment) (items : List Nat) (size : Nat) (measured : size=items.length)
    (valid : ∀ symbol∈items,symbol<E.alphabetSize) : E.StoppedWord :=
  ⟨size,fun index =>
    let inside : index.val < items.length := lt_of_lt_of_eq index.isLt measured
    ⟨items[index.val]'inside,valid _ (List.getElem_mem inside)⟩⟩

theorem wordAtLength_value (E : BinaryExperiment) (items : List Nat) (size : Nat) (measured : size=items.length)
    (valid : ∀ symbol∈items,symbol<E.alphabetSize) :
    wordAtLength E items size measured valid=
      ⟨items.length,fun index => ⟨items[index.val],valid _ (List.getElem_mem index.isLt)⟩⟩ := by
  subst size
  rfl

def wordCalculation (E : BinaryExperiment) (items : List Nat)
    (valid : ∀ symbol∈items,symbol<E.alphabetSize) : E.StoppedWord×Nat :=
  let measured:=count items
  let word:=wordAtLength E items measured.1 (count_spec items).1 valid
  (word,measured.2+4)

theorem wordCalculation_value (E : BinaryExperiment) (items : List Nat)
    (valid : ∀ symbol∈items,symbol<E.alphabetSize) :
    (wordCalculation E items valid).1=
      ⟨items.length,fun index => ⟨items[index.val],valid _ (List.getElem_mem index.isLt)⟩⟩ := by
  exact wordAtLength_value E items (count items).1 (count_spec items).1 valid

theorem wordCalculation_work (E : BinaryExperiment) (items : List Nat)
    (valid : ∀ symbol∈items,symbol<E.alphabetSize) :
    (wordCalculation E items valid).2≤8*(items.length+1) := by
  dsimp only [wordCalculation]
  have measured:=(count_spec items).2
  omega

structure WordCall (input : StatisticalInput I) where
  stage : I.Stage
  target : Rat
  word : (input.experiment stage).StoppedWord

structure TestingCalculation (input : StatisticalInput I) where
  action : Action I
  scalar : List (ScalarCall I)
  words : List (WordCall input)
  administration : Nat

def testingCalculation (input : StatisticalInput I) (quota : I.Stage→Nat×Nat)
    (stage : I.Stage) (observations : List Nat) (data : Kernel I) : TestingCalculation input :=
  match data.classification with
  | none => ⟨.abandon,[],[],4⟩
  | some .infiniteRank => ⟨.write stage false,[],[],4⟩
  | some .noTool | some (.finiteBad _) =>
      match data.target with
      | none => ⟨.abandon,[],[],8⟩
      | some target =>
          let checked:=validate (fun symbol => decide (symbol<(input.experiment stage).alphabetSize)) observations
          if valid : checked.1=true then
            have inside : ∀ symbol∈observations,symbol<(input.experiment stage).alphabetSize := by
              simpa only [checked,validate_value,List.all_eq_true,decide_eq_true_eq] using valid
            let measured:=wordCalculation (input.experiment stage) observations inside
            let word:=measured.1
            let quotaValue:=quota stage
            let odds:=(input.experiment stage).rationalWordOdds word
            let hit:=decide (odds≤target/(1-target) ∨ (1-target)/target≤odds)
            let choice:=decide (1≤odds)
            ⟨if hit then .write stage choice else
                if word.1<quotaValue.1 then .review stage else .abandon,
              [.word stage target word.1],[⟨stage,target,word⟩],
              checked.2+measured.2+quotaValue.2+24⟩
          else ⟨.abandon,[],[],checked.2+12⟩

theorem testingCalculation_value (input : StatisticalInput I) (quota : I.Stage→Nat×Nat)
    (cache : ReferenceReplayCache I) (stage : I.Stage) (data : Kernel I) :
    (testingCalculation input quota stage (historyObservations cache.seen stage) data).action=
      (testingWork input (fun i => (quota i).1) cache stage data).1 := by
  unfold testingCalculation testingWork
  cases data.classification with
  | none => rfl
  | some kind =>
      cases kind with
      | infiniteRank => rfl
      | noTool | finiteBad depth =>
          cases data.target with
          | none => rfl
          | some target =>
              dsimp only
              have valid :
                  (validate (fun symbol => decide (symbol<(input.experiment stage).alphabetSize))
                    (historyObservations cache.seen stage)).1=true ↔
                    ∀ symbol∈historyObservations cache.seen stage,symbol<(input.experiment stage).alphabetSize := by
                simp only [validate_value,List.all_eq_true,decide_eq_true_eq]
              by_cases inside : ∀ symbol∈historyObservations cache.seen stage,
                  symbol<(input.experiment stage).alphabetSize
              · simp only [dite_eq_left inside,dite_eq_left (valid.mpr inside),wordCalculation_value]
                rfl
              · simp only [dite_eq_right inside,dite_eq_right (fun h => inside (valid.mp h))]

theorem testingCalculation_bounds (input : StatisticalInput I) (quota : I.Stage→Nat×Nat)
    (stage : I.Stage) (observations : List Nat) (data : Kernel I) :
    (testingCalculation input quota stage observations data).scalar.length≤1 ∧
    (testingCalculation input quota stage observations data).words.length≤1 ∧
    (testingCalculation input quota stage observations data).administration≤
      16*(observations.length+1)+(quota stage).2+32 := by
  dsimp only [testingCalculation]
  cases data.classification with
  | none => simp
  | some kind =>
      cases kind with
      | infiniteRank => simp
      | noTool | finiteBad depth =>
          cases data.target with
          | none => simp
          | some target =>
              dsimp only
              have checked:=validate_work (fun symbol => decide (symbol<(input.experiment stage).alphabetSize)) observations
              by_cases valid : (validate (fun symbol => decide (symbol<(input.experiment stage).alphabetSize)) observations).1=true
              · rw [dite_eq_left valid]
                have inside : ∀ symbol∈observations,symbol<(input.experiment stage).alphabetSize := by
                  simpa only [validate_value,List.all_eq_true,decide_eq_true_eq] using valid
                have measured:=wordCalculation_work (input.experiment stage) observations inside
                dsimp only
                simp only [List.length_cons,List.length_nil]
                exact ⟨by omega,by omega,by omega⟩
              · rw [dite_eq_right valid]
                dsimp only
                simp only [List.length_nil]
                exact ⟨by omega,by omega,by omega⟩

def decisionCalculation (input : StatisticalInput I) (quota : I.Stage→Nat×Nat)
    (cache : ReferenceReplayCache I) (view : Snapshot I) (data : Kernel I) : TestingCalculation input :=
  if cache.halted then ⟨.stop,[],[],4⟩ else
  match view.stage with
  | none => ⟨if view.cursor=I.stageCount then .stop else .abandon,[],[],8⟩
  | some stage =>
      match cache.phase with
      | .testing => testingCalculation input quota stage view.observations data
      | .written => ⟨.abandon,[],[],8⟩
      | .reported =>
          ⟨if view.correct then .advance stage else
            match data.current,view.handle,data.repair with
            | some _,some handle,some tool => .allocate handle tool
            | _,_,_ => .abandon,[],[],24⟩
      | .allocated tool => ⟨match view.handle with
          | none => .abandon | some handle => .execute handle tool,[],[],16⟩
      | .executed _ => ⟨.advance stage,[],[],8⟩

theorem snapshot_handle (cache : ReferenceReplayCache I) (stage : I.Stage)
    (actual : referenceReplayStage I cache=some stage) :
    (RootPaper.Reference.snapshot cache).handle=referenceVisibleHandle cache.seen stage := by
  rw [snapshot_some cache stage actual]
  rfl

theorem decisionCalculation_value (input : StatisticalInput I) (quota : I.Stage→Nat×Nat)
    (cache : ReferenceReplayCache I) (data : Kernel I) :
    (decisionCalculation input quota cache (RootPaper.Reference.snapshot cache) data).action=
      (decisionBody input (fun i => (quota i).1) cache data).1 := by
  unfold decisionCalculation decisionBody
  cases halted : cache.halted with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true,ite_false]
      rw [snapshot_stage]
      cases current : referenceReplayStage I cache with
      | none => rw [snapshot_none cache current]
      | some stage =>
          dsimp only
          cases cache.phase with
          | testing =>
              rw [snapshot_some cache stage current]
              exact testingCalculation_value input quota cache stage data
          | written => rfl
          | reported =>
              rw [snapshot_correct cache stage current,snapshot_handle cache stage current]
              cases referenceReplayCorrect cache stage with
              | true => rfl
              | false =>
                  cases data.current <;> cases referenceVisibleHandle cache.seen stage <;>
                    cases data.repair <;> rfl
          | allocated tool =>
              rw [snapshot_handle cache stage current]
              cases referenceVisibleHandle cache.seen stage <;> rfl
          | executed tool => rfl

end RootPaper.Reference.Charged
