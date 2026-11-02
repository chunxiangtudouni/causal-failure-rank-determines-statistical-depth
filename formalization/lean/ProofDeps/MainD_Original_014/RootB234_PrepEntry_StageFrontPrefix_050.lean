module

public import RootB234_PrepEntry_StageBodyRun_049

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageFront

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep PSTRTMWordPreparationFront214

variable {C : Type*} {I : Instance}

structure Segment (caller : Statement C) (before final : State C) (cost : Nat) where
  trace : List (State C)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final
  count : trace.length≤cost

def Segment.append {caller : Statement C} {before middle final : State C} {A B : Nat}
    (front : Segment caller before middle A) (back : Segment caller middle final B) : Segment caller before final (A+B) := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.first
    rw [same]; rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.first]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have a:=front.count
    have b:=back.count
    simp only [List.length_append,List.length_tail]
    omega

def prefixTime (input : StatisticalInput I) (contract : Contract I) (budget : Rat) : Nat :=
  (16*((preparationInput input contract budget).length+1)^2+1)+2+FirstRaw.bodyTime input contract budget

/-- The guard is executed at the real N archive. The current header Bool
then survives the entire actual J/alphabet/prior body, before selecting
the zero-stage exit or the real observation-fee read. -/
theorem actual_prefix (caller : Statement C) (context : C) (background : RatInput.Stack → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ (trace : List (State C)) (final : State C) (left : List Bool),
      trace.head?=some (entry context background (preparationInput input contract budget)) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some .select ∧
      final.var.2.2=decide (I.stageCount≠0) ∧
      final.stk 14=NatField.packet (FirstRaw.lastNatural input contract) (background 14) ∧
      final.stk 13=RatInput.Encoder.packet (FirstRaw.firstValue input budget) (background 13) ∧
      final.stk 7=background 7 ∧
      NatPrefix.tape final.stk=Tape.mk₂ left (FirstRaw.wireSuffix input contract budget++[true]) ∧
      callerContext final.var=context ∧
      (∀ slot,¬FirstRaw.Work slot→final.stk slot=background slot) ∧
      trace.length≤prefixTime input contract budget := by
  let initialContext : FirstRaw.HeaderContext C:=(((context,default),default),default)
  obtain ⟨hRun,hFinal,hFirst,hChain,hLast,hActive,hTape,hTime,hFrames,_hMass⟩:=
    PrepHeader.header_actual initialContext background input contract budget
  have hPath:=header_path caller hRun _ hFinal hFirst hChain hLast hActive
  have hContext:=(hFrames hFinal (List.mem_of_getLast? hLast)).1
  have wholeLeft:=congrArg Tape.left hTape
  change ListBlank.mk (hFinal.stk 1)=ListBlank.mk
    (fieldLeft [] (preparationData input contract budget).length I.stageCount) at wholeLeft
  have physical:=StageGuard.physical_header hFinal.stk (preparationData input contract budget).length I.stageCount wholeLeft
  let gMemory:=(guardIso C).symm hFinal.var
  let gRun:=StageGuard.actualTrace gMemory.1 gMemory.2 hFinal.stk I.stageCount
  let gFinal:=StageGuard.final gMemory.1 hFinal.stk I.stageCount
  have gPath:=guard_path caller gMemory.1 gMemory.2 hFinal.stk I.stageCount physical
  have gShared : guardCfg (StageGuard.before gMemory.1 gMemory.2 hFinal.stk)=headerCfg hFinal := by
    cases hFinal with
    | mk point memory contents =>
      change point=some 1 at hActive
      subst point
      change (⟨some (.guard 0),guardIso C ((guardIso C).symm memory),contents⟩ : State C)=_
      rw [Equiv.apply_symm_apply]
      rfl
  let bBefore : FirstRaw.State C:=⟨some (.tools 0),(guardCfg gFinal).var,hFinal.stk⟩
  have bShared : bodyCfg bBefore=guardCfg gFinal := by
    by_cases zero : I.stageCount=0 <;>
      simp [bBefore,gFinal,StageGuard.final,guardCfg,bodyCfg,bodyLabel,guardLabel,
        LabelMap.configuration,StoreIso.configuration,zero]
  have bControl : bBefore.var.1.1.2.1=0 := by
    have saved:=congrArg (fun value : FirstRaw.HeaderContext C => value.1.2) hContext
    change hFinal.var.1.1.2=default at saved
    change hFinal.var.1.1.2.1=0
    rw [saved]; rfl
  have bPhysical : NatPrefix.tape bBefore.stk=Tape.mk₂
      (fieldLeft [] (preparationData input contract budget).length I.stageCount)
      (false::(encodeNat I.toolCount++NJ.afterTools input contract budget)) := by
    rw [show NatPrefix.tape bBefore.stk=_ from hTape,NJ.preparationTail_tools]
  obtain ⟨bRun,bFinal,left,bFirst,bChain,bLast,bActive,bNatural,bPrior,bScratch,bTape,bContext,bFrames,bTime,bHeader⟩:=
    FirstRaw.actual_body bBefore input contract budget rfl bControl bPhysical
  have bPath:=body_path caller bRun bBefore bFinal bFirst bChain bLast bActive
  let headerSegment : Segment caller (entry context background (preparationInput input contract budget))
      (headerCfg hFinal) (16*((preparationInput input contract budget).length+1)^2+1):=
    ⟨hRun.map headerCfg,hPath.1,hPath.2.1,hPath.2.2,by simpa only [List.length_map] using hTime⟩
  let guardSegment : Segment caller (headerCfg hFinal) (guardCfg gFinal) 2:=
    ⟨gRun.map guardCfg,gPath.1.trans (congrArg some gShared),gPath.2.1,gPath.2.2,by rfl⟩
  let bodySegment : Segment caller (guardCfg gFinal) (bodyCfg bFinal) (FirstRaw.bodyTime input contract budget):=
    ⟨bRun.map bodyCfg,bPath.1.trans (congrArg some bShared),bPath.2.1,bPath.2.2,
      by simpa only [List.length_map] using bTime⟩
  let whole:=(headerSegment.append guardSegment).append bodySegment
  have savedFlag : (bodyCfg bFinal).var.2.2=decide (I.stageCount≠0) := by
    change bFinal.var.2.2=decide (I.stageCount≠0)
    rw [bHeader]
    rfl
  have contextEq : callerContext (bodyCfg bFinal).var=context := by
    change FirstRaw.callerContext bFinal.var=context
    rw [bContext]
    exact congrArg (fun value : FirstRaw.HeaderContext C => value.1.1.1) hContext
  have frames : ∀ slot,¬FirstRaw.Work slot→(bodyCfg bFinal).stk slot=background slot := by
    intro slot untouched
    have notZero : slot≠0 := by intro same; subst slot; exact untouched (by decide)
    have notOne : slot≠1 := by intro same; subst slot; exact untouched (by decide)
    exact (bFrames slot untouched).trans ((hFrames hFinal (List.mem_of_getLast? hLast)).2 slot notZero notOne)
  refine ⟨whole.trace,bodyCfg bFinal,left,whole.first,whole.chain,whole.last,?_,savedFlag,?_,?_,?_,bTape,
    contextEq,frames,whole.count⟩
  · change Option.map bodyLabel bFinal.l=some .select
    rw [bActive]; rfl
  · change bFinal.stk 14=_
    rw [bNatural]
    rw [(hFrames hFinal (List.mem_of_getLast? hLast)).2 14 (by decide) (by decide)]
  · change bFinal.stk 13=_
    rw [bPrior]
    rw [(hFrames hFinal (List.mem_of_getLast? hLast)).2 13 (by decide) (by decide)]
  · change bFinal.stk 7=_
    rw [bScratch]
    exact (hFrames hFinal (List.mem_of_getLast? hLast)).2 7 (by decide) (by decide)

end RootB234.PrepEntry.StageFront
