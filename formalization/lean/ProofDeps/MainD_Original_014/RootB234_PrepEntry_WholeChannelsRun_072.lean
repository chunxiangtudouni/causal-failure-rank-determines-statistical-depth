module

public import RootB234_PrepEntry_WholeChannelsCode_071

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.WholeChannels

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*} {I : Instance}

structure Segment (caller : Statement C) (before final : State C) where
  trace : List (State C)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final

def Segment.append {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) : Segment caller before final := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.first
    rw [same]; rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_⟩
  · rw [List.head?_append,front.first]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)

theorem append_count {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    (front.append back).trace.length≤front.trace.length+back.trace.length := by
  change (front.trace++back.trace.tail).length≤_
  simp only [List.length_append,List.length_tail]
  omega

/-- The entire stage store was already present as the budget caller
context at literal entry, and Budget029 really preserves that WHOLE
value. Thus this equality neither allocates/reset flags nor reloads0. -/
theorem shared (context : C) (bits : List Bool) (stages tools : Nat) (budget : Rat)
    (final : Budget.State (StageChannels.Store C)) (active : final.l=some .done)
    (memory : Budget.callerContext final.var=stageMemory context)
    (contents : final.stk=Budget.outputBank bits stages tools budget) :
    budgetCfg final=channelsCfg ((budgetIso C) final.var).1
      (StageChannels.entry context (Budget.outputBank bits stages tools budget) bits) := by
  cases final with
  | mk point registers bank =>
    change point=some .done at active
    subst point
    change Budget.callerContext registers=stageMemory context at memory
    change bank=Budget.outputBank bits stages tools budget at contents
    change (⟨some (.channels default),(mapBudgetContext (fun _ => ()) registers,Budget.callerContext registers),bank⟩ : State C)=
      ⟨some (.channels default),(mapBudgetContext (fun _ => ()) registers,stageMemory context),
        (StageChannels.entry context (Budget.outputBank bits stages tools budget) bits).stk⟩
    rw [memory,contents,StageChannels.entry_slots]
    congr 1
    funext slot
    fin_cases slot <;> rfl

def time (input : StatisticalInput I) (contract : Contract I) (budget : Rat) : Nat :=
  Budget.coefficient*((preparationInput input contract budget).length+1)^3+
    StageChannels.coefficient*(StageChannels.scale
      (Budget.outputBank (preparationInput input contract budget) I.stageCount I.toolCount budget)
      (preparationInput input contract budget).length)^4

/-- One fixed source from literal original input: real metadata
preparation/copies/rewinds, then the actual original two-channel scan.
No packet, empty scratch, width, trace, fuel or initialized stage memory
is supplied by the original caller. -/
theorem actual (caller : Statement C) (context : C) (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (entry context (preparationInput input contract budget)) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some .done ∧ callerContext final.var=context ∧
      final.stk 8=NatField.packet I.stageCount [] ∧ final.stk 9=NatField.packet I.toolCount [] ∧
      final.stk 15=RatInput.Encoder.packet budget [] ∧
      final.stk 14=NatField.packet (FirstRaw.lastNatural input contract) [] ∧
      final.stk 13=RatInput.Encoder.packet (FirstRaw.firstValue input budget) [] ∧
      final.stk 12=StageFront.feeOutput input [] ∧
      final.stk 2=StageChannels.archive input false [] ∧ final.stk 6=StageChannels.archive input true [] ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (StageChannels.afterChannels input contract budget++[true]) ∧
      final.stk 7=[] ∧ final.stk 4=[] ∧ final.stk 3=[] ∧ final.stk 5=[] ∧
      trace.length≤time input contract budget := by
  let bits:=preparationInput input contract budget
  let background:=Budget.outputBank bits I.stageCount I.toolCount budget
  obtain ⟨bRun,bFinal,bFacts⟩:=Budget.actual_polynomial (stageMemory context) input contract budget
  have budgetPath:=budget_path caller bRun _ bFinal bFacts.first bFacts.chain bFacts.last bFacts.active
  let budgetPart : Segment caller (entry context bits) (budgetCfg bFinal):=
    ⟨bRun.map budgetCfg,budgetPath.1,budgetPath.2.1,budgetPath.2.2⟩
  let finiteMemory:=((budgetIso C) bFinal.var).1
  obtain ⟨cRun,cFinal,cFacts⟩:=StageChannels.actual_polynomial context background input contract budget rfl
  have channelPath:=channels_path caller finiteMemory cRun _ cFinal cFacts.first cFacts.chain cFacts.last cFacts.active
  have joined:=shared context bits I.stageCount I.toolCount budget bFinal bFacts.active bFacts.context_eq bFacts.contents
  let channelPart : Segment caller (budgetCfg bFinal) (channelsCfg finiteMemory cFinal):=
    ⟨cRun.map (channelsCfg finiteMemory),channelPath.1.trans (congrArg some joined.symm),channelPath.2.1,channelPath.2.2⟩
  let whole:=budgetPart.append channelPart
  refine ⟨whole.trace,channelsCfg finiteMemory cFinal,whole.first,whole.chain,whole.last,?_,cFacts.context_eq,
    ?_,?_,?_,?_,?_,?_,?_,?_,cFacts.cursor,?_,cFacts.empty4,?_,?_,?_⟩
  · change cFinal.l.map channelsLabel=some .done
    rw [cFacts.active]; rfl
  · simpa [background,Budget.outputBank,channelsCfg,LabelMap.configuration,ContextLift.configuration] using cFacts.outside 8 (by decide)
  · simpa [background,Budget.outputBank,channelsCfg,LabelMap.configuration,ContextLift.configuration] using cFacts.outside 9 (by decide)
  · simpa [background,Budget.outputBank,channelsCfg,LabelMap.configuration,ContextLift.configuration] using cFacts.outside 15 (by decide)
  · simpa [background,Budget.outputBank,channelsCfg,LabelMap.configuration,ContextLift.configuration] using cFacts.natural
  · simpa [background,Budget.outputBank,channelsCfg,LabelMap.configuration,ContextLift.configuration] using cFacts.rational
  · simpa [background,Budget.outputBank,channelsCfg,LabelMap.configuration,ContextLift.configuration] using cFacts.fee
  · simpa [background,Budget.outputBank,channelsCfg,LabelMap.configuration,ContextLift.configuration] using cFacts.archive_false
  · simpa [background,Budget.outputBank,channelsCfg,LabelMap.configuration,ContextLift.configuration] using cFacts.archive_true
  · simpa [background,Budget.outputBank,channelsCfg,LabelMap.configuration,ContextLift.configuration] using cFacts.scratch
  · simpa [background,Budget.outputBank,channelsCfg,LabelMap.configuration,ContextLift.configuration] using cFacts.outside 3 (by decide)
  · simpa [background,Budget.outputBank,channelsCfg,LabelMap.configuration,ContextLift.configuration] using cFacts.outside 5 (by decide)
  · have frontTime : budgetPart.trace.length≤Budget.coefficient*(bits.length+1)^3 := by
      simpa only [budgetPart,List.length_map] using bFacts.time
    have backTime : channelPart.trace.length≤StageChannels.coefficient*(StageChannels.scale background bits.length)^4 := by
      simpa only [channelPart,List.length_map] using cFacts.time
    exact (append_count budgetPart channelPart).trans (Nat.add_le_add frontTime backTime)

end RootB234.PrepEntry.WholeChannels
