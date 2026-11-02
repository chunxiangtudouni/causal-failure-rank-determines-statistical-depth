module
public import RootPaper_Reference_ChargedDecision012
public import RootPaper_Reference_ChargedReplay013

/-! The complete dedicated reference controller. Snapshot values are shared
between final replay guards, the kernel and the decision. Failed replay and
abandonment retain their performed work. This is not a generic interpreter. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RootPaper.Reference
variable {I : Instance}

def equalHistory : List (VisibleEvent I)→List (VisibleEvent I)→Bool×Nat
  | [],[] => (true,1)
  | [],_::_ | _::_,[] => (false,2)
  | first::left,second::right =>
      if first=second then
        let later:=equalHistory left right
        (later.1,later.2+4)
      else (false,3)

theorem equalHistory_value (left right : List (VisibleEvent I)) :
    (equalHistory left right).1=decide (left=right) := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons first left ih =>
      cases right with
      | nil => rfl
      | cons second right =>
          by_cases same : first=second
          · subst second
            simpa only [equalHistory,List.cons.injEq,true_and,ite_true] using ih right
          · simp only [equalHistory,List.cons.injEq,same,false_and,decide_false,ite_false]

theorem equalHistory_work (left right : List (VisibleEvent I)) :
    (equalHistory left right).2≤4*(left.length+right.length+1) := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => change (1 : Nat)≤4;omega
      | cons item rest => simp only [equalHistory,List.length_nil,List.length_cons];omega
  | cons first left ih =>
      cases right with
      | nil => simp only [equalHistory,List.length_nil,List.length_cons];omega
      | cons second right =>
          have tail:=ih right
          dsimp only [equalHistory]
          split_ifs <;> simp only [List.length_cons] <;> omega

structure ReadyCalculation (I : Instance) where
  view : Snapshot I
  valid : Bool
  administration : Nat

def readyCalculation (cache : ReferenceReplayCache I) (history : List (VisibleEvent I)) : ReadyCalculation I :=
  let view:=snapshotCalculation cache
  let reports:=count cache.events
  let same:=equalHistory cache.seen history
  ⟨view.1,decide (cache.phase≠.written ∧ reports.1≤I.stageCount ∧ view.1.cursor≤I.stageCount ∧ same.1),
    view.2+reports.2+same.2+24⟩

theorem snapshot_cursor (cache : ReferenceReplayCache I) :
    (RootPaper.Reference.snapshot cache).cursor=historyCursor cache.seen := by
  unfold RootPaper.Reference.snapshot
  cases referenceReplayStage I cache <;> rfl

theorem readyCalculation_value (cache : ReferenceReplayCache I) (history : List (VisibleEvent I)) :
    (readyCalculation cache history).view=RootPaper.Reference.snapshot cache ∧
    (readyCalculation cache history).valid=
      decide (cache.phase≠.written ∧ cache.events.length≤I.stageCount ∧
        historyCursor cache.seen≤I.stageCount ∧ cache.seen=history) := by
  simp only [readyCalculation,snapshotCalculation_value,(count_spec _).1,equalHistory_value,
    decide_eq_true_eq,snapshot_cursor]
  exact ⟨trivial,trivial⟩

theorem readyCalculation_work (cache : ReferenceReplayCache I) (history : List (VisibleEvent I)) :
    (readyCalculation cache history).administration≤
      (6*I.toolCount+128)*(cache.seen.length+cache.events.length+history.length+1)+64 := by
  have view:=snapshotCalculation_work cache
  have reports:=(count_spec cache.events).2
  have same:=equalHistory_work cache.seen history
  dsimp only [readyCalculation]
  nlinarith

structure ParsedCalculation (I : Instance) where
  value : Option (ReferenceReplayCache I×Snapshot I)
  ranks : List (RankCall I)
  scalar : List (ScalarCall I)
  administration : Nat

def parseCalculation (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (history : List (VisibleEvent I)) : ParsedCalculation I :=
  let run:=replayCalculation input available budget (referenceReplayInitial I) history
  match run.value with
  | none => ⟨none,run.ranks,run.scalar,run.administration+8⟩
  | some cache =>
      let ready:=readyCalculation cache history
      ⟨if 0<budget ∧ budget≤1/2 ∧ ready.valid then some (cache,ready.view) else none,
        run.ranks,run.scalar,run.administration+ready.administration+24⟩

theorem parseCalculation_value (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (history : List (VisibleEvent I)) :
    (parseCalculation input available budget history).value.map Prod.fst=
      referenceAvailableReplay input available budget history := by
  simp only [parseCalculation,replayCalculation_value]
  cases parsed : history.foldlM (referenceAvailableStep input available budget) (referenceReplayInitial I) with
  | none =>
      unfold referenceAvailableReplay
      rw [parsed]
      by_cases valid : 0<budget ∧ budget≤1/2
      · rw [ite_eq_left valid];rfl
      · rw [ite_eq_right valid];rfl
  | some cache =>
      dsimp only
      rw [(readyCalculation_value cache history).2]
      unfold referenceAvailableReplay
      rw [parsed]
      by_cases valid : 0<budget ∧ budget≤1/2
      · rw [ite_eq_left valid]
        dsimp only
        simp only [valid.1,valid.2,true_and,decide_eq_true_eq]
        change (if cache.phase≠.written ∧ cache.events.length≤I.stageCount ∧
            historyCursor cache.seen≤I.stageCount ∧ cache.seen=history
          then some (cache,(readyCalculation cache history).view) else none).map Prod.fst=
          if cache.phase≠.written ∧ cache.events.length≤I.stageCount ∧
            historyCursor cache.seen≤I.stageCount ∧ cache.seen=history then some cache else none
        split_ifs <;> rfl
      · have invalid : ¬(0<budget ∧ budget≤1/2 ∧
            decide (cache.phase≠.written ∧ cache.events.length≤I.stageCount ∧
              historyCursor cache.seen≤I.stageCount ∧ cache.seen=history)=true) := by
          intro alleged
          exact valid ⟨alleged.1,alleged.2.1⟩
        rw [ite_eq_right invalid,ite_eq_right valid]
        rfl

theorem parseCalculation_view (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I) (view : Snapshot I)
    (actual : (parseCalculation input available budget history).value=some (cache,view)) :
    view=RootPaper.Reference.snapshot cache := by
  unfold parseCalculation at actual
  cases parsed : (replayCalculation input available budget (referenceReplayInitial I) history).value with
  | none => simp only [parsed] at actual;cases actual
  | some next =>
      simp only [parsed] at actual
      split_ifs at actual with valid
      · have same:=Option.some.inj actual
        have first:=congrArg Prod.fst same
        have second:=congrArg Prod.snd same
        dsimp only at first second
        subst cache
        exact second.symm.trans (readyCalculation_value next history).1

structure ControllerCalculation (input : StatisticalInput I) where
  action : Action I
  ranks : List (RankCall I)
  scalar : List (ScalarCall I)
  words : List (WordCall input)
  administration : Nat

def controllerCalculation (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (quota : I.Stage→Nat×Nat) (history : List (VisibleEvent I)) : ControllerCalculation input :=
  let replayed:=parseCalculation input available budget history
  match replayed.value with
  | none => ⟨.abandon,replayed.ranks,replayed.scalar,[],replayed.administration+4⟩
  | some (cache,view) =>
      let data:=kernelCalculation available budget cache view
      let decision:=decisionCalculation input quota cache view data.1
      ⟨decision.action,replayed.ranks++data.1.ranks,replayed.scalar++data.1.scalar++decision.scalar,
        decision.words,replayed.administration+data.2+decision.administration+16⟩

attribute [local irreducible] kernel

theorem controllerCalculation_candidate (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (quota : I.Stage→Nat×Nat) (history : List (VisibleEvent I)) :
    (controllerCalculation input available budget quota history).action=
      referenceCandidateAction input available budget (some (fun stage => (quota stage).1)) history := by
  have value:=parseCalculation_value input available budget history
  cases parsed : (parseCalculation input available budget history).value with
  | none =>
      rw [parsed] at value
      simp only [Option.map_none] at value
      simp only [controllerCalculation,parsed,referenceCandidateAction,←value]
  | some pair =>
      rcases pair with ⟨cache,view⟩
      have correct:=parseCalculation_view input available budget history cache view parsed
      rw [parsed] at value
      have original : referenceAvailableReplay input available budget history=some cache := value.symm
      have seen:=(referenceAvailableReplay_some_spec input available budget history cache original).2.2.2.2.2
      simp only [controllerCalculation,parsed]
      rw [kernelCalculation_value _ _ _ _ correct,correct,decisionCalculation_value,
        decisionBody_value]
      simp only [referenceCandidateAction,original]
      rw [←seen]
      rfl

theorem controllerCalculation_same_rule {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (early : C.reporting=.early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : Rat) (positive : 0<budget) (small : budget≤1/2) (quota : I.Stage→Nat×Nat)
    (seed : Seed) (truth : I.Stage→Bool) (tapes : ReviewTapes input) {n : Nat} {state : State I}
    (hp : Prefix input C .uncapped accounting
      (referenceRule input available budget (some (fun stage => (quota stage).1))) seed truth tapes n state) :
    (controllerCalculation input available budget quota state.history).action=
      referenceRule input available budget (some (fun stage => (quota stage).1)) seed state.history := by
  exact (controllerCalculation_candidate input available budget quota state.history).trans
    (referenceRule_eq_candidate_of_prefix input C early accounting available budget positive small _
      seed truth tapes hp).symm

end RootPaper.Reference.Charged
