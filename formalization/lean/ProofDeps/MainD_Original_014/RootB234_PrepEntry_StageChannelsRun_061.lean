module

public import RootB234_PrepEntry_StageChannelsTransportBounds_064
public import RootB234_PrepEntry_StageChannelsBuildBounds_065

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageChannels

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*} {I : Instance}

instance (right : Bool) (slot : RatInput.Stack) : Decidable (LoopFrame right slot) := by
  unfold LoopFrame
  infer_instance

def values (experiment : BinaryExperiment) (truth : Bool) : List Rat :=
  (List.finRange experiment.alphabetSize).map (fun symbol => experiment.channel truth symbol)

def archive (input : StatisticalInput I) (truth : Bool) (tail : List Bool) : List Bool :=
  if positive : 0<I.stageCount then Channels.archived (values (input.experiment ⟨0,positive⟩) truth) tail else tail

def afterChannels (input : StatisticalInput I) (contract : Contract I) (budget : Rat) : List Bool :=
  if _positive : 0<I.stageCount then (FirstRaw.afterFirstExperiment input contract budget).flatMap encodeDatum else []

def Work (slot : RatInput.Stack) : Prop :=
  StageFront.Work slot ∨ slot=2 ∨ slot=4 ∨ slot=6 ∨ slot=10 ∨ slot=11
instance (slot : RatInput.Stack) : Decidable (Work slot) := by unfold Work; infer_instance

def frontCap (background : RatInput.Stack → List Bool) (input : StatisticalInput I) (contract : Contract I) (budget : Rat) : Nat :=
  StageFront.coefficient*(StageFront.scale background (preparationInput input contract budget).length)^2

def totalTime (background : RatInput.Stack → List Bool) (input : StatisticalInput I) (contract : Contract I) (budget : Rat) : Nat :=
  let cap:=frontCap background input contract budget
  if positive : 0<I.stageCount then
    let experiment:=input.experiment ⟨0,positive⟩
    let leftBound:=buildSpace experiment.alphabetSize cap
    let afterLeft:=leftBound+Bounds.credits (values experiment false)
    cap+2+buildLimit experiment.alphabetSize cap+Bounds.limit (values experiment false) leftBound+
      buildLimit experiment.alphabetSize afterLeft+Bounds.limit (values experiment true) (buildSpace experiment.alphabetSize afterLeft)
  else cap+2

theorem afterFee_exact (input : StatisticalInput I) (contract : Contract I) (budget : Rat) (positive : 0<I.stageCount) :
    StageFront.afterFee input contract budget=
      Channels.fields (values (input.experiment ⟨0,positive⟩) false)++
      Channels.fields (values (input.experiment ⟨0,positive⟩) true)++afterChannels input contract budget := by
  simp only [StageFront.afterFee,dite_eq_left positive,FirstRaw.channelValues,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.flatMap_append,Channels.fields,values,afterChannels]

/-- The original preparation source reads both complete channel vectors
in their existing order. A is physically copied from14 twice, not passed
to the source as an answer, and both packet archives have the same
reverse symbol order. The true N=0 branch performs neither loop. -/
theorem actual (caller : Statement C) (context : C) (background : RatInput.Stack → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat) (empty : background 4=[]) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (entry context background (preparationInput input contract budget)) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some .done ∧
      final.stk 14=NatField.packet (FirstRaw.lastNatural input contract) (background 14) ∧
      final.stk 13=RatInput.Encoder.packet (FirstRaw.firstValue input budget) (background 13) ∧
      final.stk 12=StageFront.feeOutput input (background 12) ∧ final.stk 7=background 7 ∧
      final.stk 2=archive input false (background 2) ∧ final.stk 6=archive input true (background 6) ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (afterChannels input contract budget++[true]) ∧
      callerContext final.var=context ∧ final.var.2.2.2=decide (I.stageCount≠0) ∧
      final.stk 4=[] ∧ (∀ slot,¬Work slot→final.stk slot=background slot) ∧
      trace.length≤totalTime background input contract budget := by
  obtain ⟨oldTrace,oldFinal,facts⟩:=StageFront.actual_polynomial context background input contract budget
  have frontPath:=front_path caller default oldTrace _ oldFinal facts.first facts.chain facts.last facts.active
  let front : Segment caller (entry context background (preparationInput input contract budget)) (frontCfg default oldFinal):=
    ⟨oldTrace.map (frontCfg default),frontPath.1,frontPath.2.1,frontPath.2.2⟩
  have frontActive : (frontCfg (C := C) default oldFinal).l=some .select := by
    change oldFinal.l.map frontLabel=some .select
    rw [facts.active]; rfl
  have frontShape : frontCfg (C := C) default oldFinal=
      (⟨some .select,(default,oldFinal.var),oldFinal.stk⟩ : State C) := by
    cases oldFinal with
    | mk point memory bank =>
      change point.map frontLabel=some .select at frontActive
      change (⟨point.map frontLabel,(default,memory),bank⟩ : State C)=_
      rw [frontActive]
  have frontTime : front.trace.length≤frontCap background input contract budget := by
    simpa only [front,List.length_map,frontCap] using facts.time
  have frontBound : ∀ slot,(oldFinal.stk slot).length≤frontCap background input contract budget :=
    (facts.boundaries oldFinal (List.mem_of_getLast? facts.last)).2.1
  by_cases positive : 0<I.stageCount
  · have nonzero : I.stageCount≠0 := by omega
    let boot : State C:=⟨some (.buildLeft 0),(frontCfg default oldFinal).var,oldFinal.stk⟩
    have selected : TM2.step (program caller) (frontCfg default oldFinal)=some boot := by
      rw [frontShape,select_step]
      simp [boot,frontShape,facts.stage_flag,nonzero]
    let selectRun : Segment caller (frontCfg default oldFinal) boot:=
      ⟨[frontCfg default oldFinal,boot],rfl,List.isChain_cons_cons.mpr ⟨selected,List.isChain_singleton _⟩,rfl⟩
    let experiment:=input.experiment ⟨0,positive⟩
    let suffix:=afterChannels input contract budget
    have natural : boot.stk 14=NatField.packet experiment.alphabetSize (background 14) := by
      simpa only [FirstRaw.lastNatural_positive input contract positive] using facts.natural
    have scratch : boot.stk 4=[] := (facts.outside 4 (by decide)).trans empty
    obtain ⟨leftStart,leftBuild,atLeft,leftBuildContext,leftCounter,leftGuard,leftScratch,leftBuildFrame,leftBuildTime,leftBuildBound⟩:=
      actual_build_bounded false caller boot experiment.alphabetSize (background 14) (frontCap background input contract budget)
        rfl natural scratch frontBound
    have count : PSTRTMIncrement009.valueDigits (PSTRTMNatValue017.rawPayload experiment.alphabetSize)=
        (values experiment false).length := by
      rw [PSTRTMNatValue017.valueDigits_rawPayload]
      simp only [values,List.length_map,List.length_finRange]
    have leftStream : ListBlank.mk (leftStart.stk 0)=ListBlank.mk
        (Channels.fields (values experiment false)++(Channels.fields (values experiment true)++suffix)++[true]) := by
      rw [leftBuildFrame 0 (by decide) (by decide) (by decide)]
      simpa only [boot,afterFee_exact input contract budget positive,List.append_assoc] using facts.cursor
    obtain ⟨leftFinal,leftRun,leftDigits,afterLeft,leftContext,leftPacket,leftStored,leftCursor,
      _leftCounter,_leftZero,_leftWidth,_leftGuard,leftEmpty,leftFrame,leftEndBound,leftTime⟩:=
      actual_loop_bounded false caller leftStart (values experiment false) _ _ _
        atLeft leftCounter leftGuard leftScratch count leftStream leftBuildBound
    have rightNatural : leftFinal.stk 14=NatField.packet experiment.alphabetSize (background 14) :=
      (leftFrame 14 (by decide)).trans ((leftBuildFrame 14 (by decide) (by decide) (by decide)).trans natural)
    obtain ⟨rightStart,rightBuild,atRight,rightBuildContext,rightCounter,rightGuard,rightScratch,rightBuildFrame,rightBuildTime,rightBuildBound⟩:=
      actual_build_bounded true caller leftFinal experiment.alphabetSize (background 14) _
        afterLeft rightNatural leftEmpty leftEndBound
    have rightCount : PSTRTMIncrement009.valueDigits (PSTRTMNatValue017.rawPayload experiment.alphabetSize)=
        (values experiment true).length := by
      rw [PSTRTMNatValue017.valueDigits_rawPayload]
      simp only [values,List.length_map,List.length_finRange]
    have rightStream : ListBlank.mk (rightStart.stk 0)=ListBlank.mk (Channels.fields (values experiment true)++suffix++[true]) := by
      rw [rightBuildFrame 0 (by decide) (by decide) (by decide)]
      exact leftCursor
    obtain ⟨final,rightRun,rightDigits,atDone,rightContext,rightPacket,rightStored,cursor,
      _rightCounter,_rightZero,_rightWidth,_rightGuard,rightEmpty,rightFrame,_rightEndBound,rightTime⟩:=
      actual_loop_bounded true caller rightStart (values experiment true) _ suffix _
        atRight rightCounter rightGuard rightScratch rightCount rightStream rightBuildBound
    change leftFinal.stk 2=Channels.archived (values experiment false) (leftStart.stk 2) at leftStored
    change final.stk 6=Channels.archived (values experiment true) (rightStart.stk 6) at rightStored
    let whole:=((((front.append selectRun).append leftBuild).append leftRun).append rightBuild).append rightRun
    have held (slot : RatInput.Stack)
        (safe : slot≠0 ∧ slot≠1 ∧ slot≠2 ∧ slot≠4 ∧ slot≠6 ∧ slot≠10 ∧ slot≠11 ∧ slot≠15) :
        final.stk slot=boot.stk slot := by
      have leftSafe : LoopFrame false slot :=
        ⟨safe.1,safe.2.1,safe.2.2.1,safe.2.2.2.1,safe.2.2.2.2.2.1,safe.2.2.2.2.2.2.1,safe.2.2.2.2.2.2.2⟩
      have rightSafe : LoopFrame true slot :=
        ⟨safe.1,safe.2.1,safe.2.2.2.2.1,safe.2.2.2.1,safe.2.2.2.2.2.1,safe.2.2.2.2.2.2.1,safe.2.2.2.2.2.2.2⟩
      exact (rightFrame slot rightSafe).trans ((rightBuildFrame slot safe.2.2.2.1 safe.2.2.2.2.2.1 safe.2.2.2.2.2.2.1).trans
        ((leftFrame slot leftSafe).trans (leftBuildFrame slot safe.2.2.2.1 safe.2.2.2.2.2.1 safe.2.2.2.2.2.2.1)))
    have wholeContext : final.var.2=oldFinal.var :=
      rightContext.trans (rightBuildContext.trans (leftContext.trans leftBuildContext))
    have archivedLeft : final.stk 2=archive input false (background 2) := by
      rw [rightFrame 2 (by decide),rightBuildFrame 2 (by decide) (by decide) (by decide),leftStored,
        leftBuildFrame 2 (by decide) (by decide) (by decide)]
      change Channels.archived (values experiment false) (oldFinal.stk 2)=_
      rw [facts.outside 2 (by decide)]
      simp only [archive,dite_eq_left positive,experiment]
    have archivedRight : final.stk 6=archive input true (background 6) := by
      rw [rightStored,rightBuildFrame 6 (by decide) (by decide) (by decide),leftFrame 6 (by decide),
        leftBuildFrame 6 (by decide) (by decide) (by decide)]
      change Channels.archived (values experiment true) (oldFinal.stk 6)=_
      rw [facts.outside 6 (by decide)]
      simp only [archive,dite_eq_left positive,experiment]
    have outside : ∀ slot,¬Work slot→final.stk slot=background slot := by
      intro slot safe
      by_cases target : slot=15
      · subst slot
        exact rightPacket.trans ((rightBuildFrame 15 (by decide) (by decide) (by decide)).trans
          (leftPacket.trans ((leftBuildFrame 15 (by decide) (by decide) (by decide)).trans (facts.outside 15 (by decide)))))
      · have combined : slot≠0 ∧ slot≠1 ∧ slot≠2 ∧ slot≠4 ∧ slot≠6 ∧ slot≠10 ∧ slot≠11 ∧ slot≠15 := by
          simp only [Work,StageFront.Work,not_or] at safe
          tauto
        exact (held slot combined).trans (facts.outside slot (fun member => safe (Or.inl member)))
    refine ⟨whole.trace,final,whole.first,whole.chain,whole.last,atDone,?_,?_,?_,?_,archivedLeft,archivedRight,
      cursor,?_,?_,rightEmpty,outside,?_⟩
    · exact (held 14 (by decide)).trans facts.natural
    · exact (held 13 (by decide)).trans facts.rational
    · exact (held 12 (by decide)).trans facts.fee
    · exact (held 7 (by decide)).trans facts.scratch
    · exact (congrArg StageFront.callerContext wholeContext).trans facts.context_eq
    · exact (congrArg (fun memory : StageFront.Store C => memory.2.2) wholeContext).trans facts.stage_flag
    · have one:=append_count front selectRun
      have two:=append_count (front.append selectRun) leftBuild
      have three:=append_count ((front.append selectRun).append leftBuild) leftRun
      have four:=append_count (((front.append selectRun).append leftBuild).append leftRun) rightBuild
      have five:=append_count ((((front.append selectRun).append leftBuild).append leftRun).append rightBuild) rightRun
      have selectTime : selectRun.trace.length=2 := rfl
      change whole.trace.length≤_
      simp only [totalTime,dite_eq_left positive]
      dsimp only [whole]
      dsimp only [experiment] at leftBuildTime leftTime rightBuildTime rightTime
      omega
  · have zero : I.stageCount=0 := by omega
    let final : State C:=⟨some .done,(frontCfg default oldFinal).var,oldFinal.stk⟩
    have selected : TM2.step (program caller) (frontCfg default oldFinal)=some final := by
      rw [frontShape,select_step]
      simp [final,frontShape,facts.stage_flag,zero]
    let selectRun : Segment caller (frontCfg default oldFinal) final:=
      ⟨[frontCfg default oldFinal,final],rfl,List.isChain_cons_cons.mpr ⟨selected,List.isChain_singleton _⟩,rfl⟩
    let whole:=front.append selectRun
    refine ⟨whole.trace,final,whole.first,whole.chain,whole.last,rfl,facts.natural,facts.rational,facts.fee,facts.scratch,
      ?_,?_,?_,facts.context_eq,facts.stage_flag,(facts.outside 4 (by decide)).trans empty,?_,?_⟩
    · simpa only [archive,dite_eq_right positive] using facts.outside 2 (by decide)
    · simpa only [archive,dite_eq_right positive] using facts.outside 6 (by decide)
    · simpa only [StageFront.afterFee,afterChannels,dite_eq_right positive] using facts.cursor
    · intro slot safe
      exact facts.outside slot (fun member => safe (Or.inl member))
    · have joined:=append_count front selectRun
      have selectTime : selectRun.trace.length=2 := rfl
      change (front.append selectRun).trace.length≤_
      simp only [totalTime,dite_eq_right positive]
      omega

end RootB234.PrepEntry.StageChannels
