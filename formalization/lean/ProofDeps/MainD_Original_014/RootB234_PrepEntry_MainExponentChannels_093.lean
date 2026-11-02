module

public import RootB234_PrepEntry_MainExponentTail_092

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.MainExponent
open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM B23_4_RatWordPrep RootB234.PrepExponent RootL01.SymbolicSource
variable {C : Type*} {I : Instance}

def channelsCfg (memory : Outer) (before : StageChannels.State C) : State C :=
  LabelMap.configuration channelsLabel (StoreIso.configuration (stageIso C) (ContextLift.configuration memory before))

theorem channels_path (caller : Statement C) (memory : Outer)
    (run : List (StageChannels.State C)) (before final : StageChannels.State C)
    (first : run.head?=some before) (chain : run.IsChain (fun a b => TM2.step (StageChannels.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map (channelsCfg memory)).head?=some (channelsCfg memory before) ∧
    (run.map (channelsCfg memory)).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map (channelsCfg memory)).getLast?=some (channelsCfg memory final) := by
  let old : StageChannels.Label → TM2.Stmt RatInput.Alphabet StageChannels.Label (Outer×StageChannels.Store C) :=
    ContextLift.machine (StageChannels.program .halt)
  have contextPath:=ContextLift.actual_path (StageChannels.program .halt) memory run before final first chain last
  have linked:=store_label_path (stageIso C) channelsLabel old caller .done rfl _ _ _
    contextPath.1 contextPath.2.1 contextPath.2.2.1 active
    (by intro point different;simp only [channelsLabel,different,ite_false,program];rfl)
  simp only [List.map_map,Function.comp_def] at linked
  exact linked

theorem channels_shared (context : C) (bits : List Bool) (stages tools : Nat) (budget : Rat)
    (memory : Global.Store (ExponentContext C)) (preserved : (QLoop.rootContext memory).2=WholeChannels.stageMemory context) :
    state (.channels default) (exponentIso C memory) (stageBank bits stages tools budget)=
      channelsCfg (((stageIso C).symm (exponentIso C memory)).1)
        (StageChannels.entry context (stageBank bits stages tools budget) bits) := by
  have actualStage : ((stageIso C).symm (exponentIso C memory)).2=WholeChannels.stageMemory context := preserved
  change (⟨some (.channels default),exponentIso C memory,stageBank bits stages tools budget⟩ : State C)=
    ⟨some (.channels default),stageIso C (((stageIso C).symm (exponentIso C memory)).1,
      (StageChannels.entry context (stageBank bits stages tools budget) bits).var),
      (StageChannels.entry context (stageBank bits stages tools budget) bits).stk⟩
  rw [WholeChannels.stage_entry_memory,←actualStage,Prod.mk.eta,Equiv.apply_symm_apply,StageChannels.entry_slots]
  congr 1
  funext slot
  fin_cases slot <;> rfl

def time (input : StatisticalInput I) (contract : Contract I) (budget : Rat) : Nat :=
  let bits:=preparationInput input contract budget
  Budget.coefficient*(bits.length+1)^3+
    Global.totalCost (metadataBank bits I.stageCount I.toolCount budget) [] budget I.stageCount+
    NatPacket.coefficient*(RatInput.occupied (exponentBank bits I.stageCount I.toolCount budget)+1)+
    (movedBank bits I.stageCount I.toolCount budget 7).length+2+
    StageChannels.coefficient*(StageChannels.scale (stageBank bits I.stageCount I.toolCount budget) bits.length)^4

/-- One fixed finite source from literal original input, now including
the complete original E producer. The E packet is physically moved to5
and its temporary7 cache is physically cleared before channel parsing. -/
theorem actual (caller : Statement C) (context : C) (input : StatisticalInput I) (contract : Contract I)
    (budget : Rat) (positive : 0<budget) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (entry context (preparationInput input contract budget)) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some .done ∧ callerContext final.var=context ∧
      final.stk 5=NatField.packet (computedExponent (I:=I) budget) [] ∧
      final.stk 8=NatField.packet I.stageCount [] ∧ final.stk 9=NatField.packet I.toolCount [] ∧
      final.stk 15=RatInput.Encoder.packet budget [] ∧
      final.stk 14=NatField.packet (FirstRaw.lastNatural input contract) [] ∧
      final.stk 13=RatInput.Encoder.packet (FirstRaw.firstValue input budget) [] ∧
      final.stk 12=StageFront.feeOutput input [] ∧
      final.stk 2=StageChannels.archive input false [] ∧ final.stk 6=StageChannels.archive input true [] ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (StageChannels.afterChannels input contract budget++[true]) ∧
      final.stk 7=[] ∧ final.stk 4=[] ∧ final.stk 3=[] ∧
      trace.length≤time input contract budget := by
  let bits:=preparationInput input contract budget
  let background:=stageBank bits I.stageCount I.toolCount budget
  obtain ⟨eMemory,front,stageMemory,_context,frontCount⟩:=through_exponent caller context input contract budget positive
  obtain ⟨moved,moveCount⟩:=natural_actual caller bits I.stageCount I.toolCount budget eMemory
  obtain ⟨cleared,clearCount⟩:=clear_actual caller bits I.stageCount I.toolCount budget (eMemory.1,false,false)
  let current:=exponentIso C (eMemory.1,false,false)
  let outer:=((stageIso C).symm current).1
  obtain ⟨cRun,cFinal,cFacts⟩:=StageChannels.actual_polynomial context background input contract budget rfl
  have channelPath:=channels_path caller outer cRun _ cFinal cFacts.first cFacts.chain cFacts.last cFacts.active
  have shared:=channels_shared context bits I.stageCount I.toolCount budget (eMemory.1,false,false) stageMemory
  let channels : Segment caller
      (state (.channels default) current background) (channelsCfg outer cFinal):=
    ⟨cRun.map (channelsCfg outer),channelPath.1.trans (congrArg some shared.symm),channelPath.2.1,channelPath.2.2⟩
  let p1:=front.append moved
  let p2:=p1.append cleared
  let whole:=p2.append channels
  refine ⟨whole.trace,channelsCfg outer cFinal,whole.first,whole.chain,whole.last,?_,cFacts.context_eq,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,cFacts.cursor,?_,cFacts.empty4,?_,?_⟩
  · change cFinal.l.map channelsLabel=some .done
    rw [cFacts.active];rfl
  · simpa [background,stageBank,computedExponent,channelsCfg,LabelMap.configuration,StoreIso.configuration,ContextLift.configuration]
      using cFacts.outside 5 (by decide)
  · simpa [background,stageBank,metadataBank,Budget.outputBank,channelsCfg,LabelMap.configuration,StoreIso.configuration,ContextLift.configuration]
      using cFacts.outside 8 (by decide)
  · simpa [background,stageBank,metadataBank,Budget.outputBank,channelsCfg,LabelMap.configuration,StoreIso.configuration,ContextLift.configuration]
      using cFacts.outside 9 (by decide)
  · simpa [background,stageBank,metadataBank,Budget.outputBank,channelsCfg,LabelMap.configuration,StoreIso.configuration,ContextLift.configuration]
      using cFacts.outside 15 (by decide)
  · simpa [background,stageBank,metadataBank,Budget.outputBank,channelsCfg,LabelMap.configuration,StoreIso.configuration,ContextLift.configuration]
      using cFacts.natural
  · simpa [background,stageBank,metadataBank,Budget.outputBank,channelsCfg,LabelMap.configuration,StoreIso.configuration,ContextLift.configuration]
      using cFacts.rational
  · simpa [background,stageBank,metadataBank,Budget.outputBank,channelsCfg,LabelMap.configuration,StoreIso.configuration,ContextLift.configuration]
      using cFacts.fee
  · simpa [background,stageBank,metadataBank,Budget.outputBank,channelsCfg,LabelMap.configuration,StoreIso.configuration,ContextLift.configuration]
      using cFacts.archive_false
  · simpa [background,stageBank,metadataBank,Budget.outputBank,channelsCfg,LabelMap.configuration,StoreIso.configuration,ContextLift.configuration]
      using cFacts.archive_true
  · simpa [background,stageBank,metadataBank,Budget.outputBank,channelsCfg,LabelMap.configuration,StoreIso.configuration,ContextLift.configuration]
      using cFacts.scratch
  · simpa [background,stageBank,metadataBank,Budget.outputBank,channelsCfg,LabelMap.configuration,StoreIso.configuration,ContextLift.configuration]
      using cFacts.outside 3 (by decide)
  · have frontBound : front.trace.length≤Budget.coefficient*(bits.length+1)^3+
      Global.totalCost (metadataBank bits I.stageCount I.toolCount budget) [] budget I.stageCount := frontCount
    have channelsCount : channels.trace.length≤StageChannels.coefficient*(StageChannels.scale background bits.length)^4 := by
      simpa only [channels,List.length_map] using cFacts.time
    have c1 : p1.trace.length≤front.trace.length+moved.trace.length:=front.append_length moved
    have c2 : p2.trace.length≤p1.trace.length+cleared.trace.length:=p1.append_length cleared
    have c3 : whole.trace.length≤p2.trace.length+channels.trace.length:=p2.append_length channels
    change whole.trace.length≤Budget.coefficient*(bits.length+1)^3+
      Global.totalCost (metadataBank bits I.stageCount I.toolCount budget) [] budget I.stageCount+
      NatPacket.coefficient*(RatInput.occupied (exponentBank bits I.stageCount I.toolCount budget)+1)+
      (movedBank bits I.stageCount I.toolCount budget 7).length+2+
      StageChannels.coefficient*(StageChannels.scale background bits.length)^4
    omega

end RootB234.PrepEntry.MainExponent
