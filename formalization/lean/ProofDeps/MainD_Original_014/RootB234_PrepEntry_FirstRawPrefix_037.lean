module

public import RootB234_PrepEntry_FirstRawSyntax_036

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.FirstRaw

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
    (front : Segment caller before middle A) (back : Segment caller middle final B) :
    Segment caller before final (A+B) := by
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
  (16*((preparationInput input contract budget).length+1)^2+1)+
  ((PSTRTMNatValue017.rawPayload I.toolCount).length^2+9*(PSTRTMNatValue017.rawPayload I.toolCount).length+5)+
  NatPrefix.workTime (firstNumbers input contract)+
  (3*(PSTRTMNatValue017.rawPayload (lastNatural input contract)).length+6)

/-- Read actual M/N/J and the original natural prefix, then export its
last field on14. This begins at the literal original-input entry with
all finite registers already allocated; 8/9/15 and arbitrary frames stay. -/
theorem actual_prefix (caller : Statement C) (context : C) (background : RatInput.Stack → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ (trace : List (State C)) (final : State C) (suffix : List Bool),
      trace.head?=some (entry context background (preparationInput input contract budget)) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some (.rational .boot) ∧
      final.stk 14=NatField.packet (lastNatural input contract) (background 14) ∧
      NatPrefix.tape final.stk=Tape.mk₂
        (NatPrefix.archived (NJ.finalLeft input contract budget) (firstNumbers input contract))
        (encodeDatum (.rational (firstValue input budget))++suffix++[true]) ∧
      (∀ slot,slot≠0→slot≠1→slot≠14→final.stk slot=background slot) ∧
      trace.length≤prefixTime input contract budget := by
  let initialContext : HeaderContext C:=(((context,default),default),default)
  obtain ⟨hRun,hFinal,hFirst,hChain,hLast,hActive,hTape,hTime,hFrames,_hMass⟩:=
    PrepHeader.header_actual initialContext background input contract budget
  have hPath:=header_path caller hRun _ hFinal hFirst hChain hLast hActive
  let aStart : Alpha.State (HeaderNat.Store (C × RawGetter.ParserMemory)):=
    ⟨some 0,(alphaIso C).symm hFinal.var,hFinal.stk⟩
  have aControl : aStart.var.2.1=0 := by
    have saved:=congrArg (fun value : HeaderContext C => value.1.2)
      (hFrames hFinal (List.mem_of_getLast? hLast)).1
    change hFinal.var.1.1.2=default at saved
    change hFinal.var.1.1.2.1=0
    rw [saved]; rfl
  have aPhysical : NatPrefix.tape hFinal.stk=Tape.mk₂
      (fieldLeft [] (preparationData input contract budget).length I.stageCount)
      (false::(encodeNat I.toolCount++NJ.afterTools input contract budget)) := by
    rw [show NatPrefix.tape hFinal.stk=_ from hTape,NJ.preparationTail_tools]
  obtain ⟨aRun,aFinal,aFirst,aChain,aLast,aActive,aTape,aTime,_aContext,aFrames⟩:=
    Alpha.actual aStart.var.1 aStart.var.2 hFinal.stk _ I.toolCount _ aControl aPhysical
  have aPath:=tools_path caller aRun aStart aFinal aFirst aChain aLast aActive
  have aShared : toolsCfg aStart=headerCfg hFinal := by
    cases hFinal with
    | mk point memory contents =>
      change point=some 1 at hActive
      subst point
      change (⟨some (.tools 0),alphaIso C ((alphaIso C).symm memory),contents⟩ : State C)=_
      rw [Equiv.apply_symm_apply]
      rfl
  let headerSegment : Segment caller (entry context background (preparationInput input contract budget))
      (headerCfg hFinal) (16*((preparationInput input contract budget).length+1)^2+1):=
    ⟨hRun.map headerCfg,hPath.1,hPath.2.1,hPath.2.2,by simpa only [List.length_map] using hTime⟩
  let toolsSegment : Segment caller (headerCfg hFinal) (toolsCfg aFinal)
      ((PSTRTMNatValue017.rawPayload I.toolCount).length^2+9*(PSTRTMNatValue017.rawPayload I.toolCount).length+5):=
    ⟨aRun.map toolsCfg,aPath.1.trans (congrArg some aShared),aPath.2.1,aPath.2.2,by
      rw [List.length_map,aTime]⟩
  obtain ⟨suffix,stream⟩:=afterTools_split input contract budget
  let pStart : NatPrefix.State (HeaderNat.Store (C × RawGetter.ParserMemory)):=
    ⟨some .check,aFinal.var,aFinal.stk⟩
  have pPhysical : NatPrefix.tape aFinal.stk=Tape.mk₂ (NJ.finalLeft input contract budget)
      (NatPrefix.naturals (firstNumbers input contract)++
        encodeDatum (.rational (firstValue input budget))++(suffix++[true])) := by
    rw [show NatPrefix.tape aFinal.stk=_ from aTape,stream]
    simp only [List.append_assoc]
    rfl
  obtain ⟨pRun,pFinal,pFirst,pChain,pLast,pActive,pTape,_pContext,pTime,pFrames⟩:=
    NatPrefix.actual .halt (firstNumbers input contract) aFinal.var.1 aFinal.var.2 aFinal.stk
      (NJ.finalLeft input contract budget) (firstValue input budget) (suffix++[true]) pPhysical
  have pPath:=prefix_path caller pRun pStart pFinal pFirst pChain pLast pActive
  have pShared : prefixCfg pStart=toolsCfg aFinal := by
    cases aFinal with
    | mk point memory contents =>
      change point=some 1 at aActive
      subst point
      rfl
  let prefixSegment : Segment caller (toolsCfg aFinal) (prefixCfg pFinal)
      (NatPrefix.workTime (firstNumbers input contract)):=
    ⟨pRun.map prefixCfg,pPath.1.trans (congrArg some pShared),pPath.2.1,pPath.2.2,
      by simpa only [List.length_map] using pTime⟩
  let fStart : NatField.State (FieldContext C):=⟨some 0,(fieldIso C).symm ((prefixCfg pFinal).var),
    StackIso.slots naturalRoles.symm pFinal.stk⟩
  have wholeLeft:=congrArg Tape.left pTape
  change ListBlank.mk (pFinal.stk 1)=ListBlank.mk
    (NatPrefix.archived (NJ.finalLeft input contract budget) (firstNumbers input contract)) at wholeLeft
  have physical:=firstNatural_physical input contract budget pFinal.stk wholeLeft
  have fPhysical : ∃ tail,fStart.stk 1=false::(PSTRTMRawNat010.leftBlocks
      (PSTRTMNatValue017.rawPayload (lastNatural input contract)).reverse++false::tail) := physical
  obtain ⟨fRun,fFinal,fFirst,fChain,fLast,fActive,_fContext,fContents,fTime⟩:=
    NatField.actual_current fStart.var fStart.stk (lastNatural input contract) fPhysical
  have fPath:=natural_path caller fRun fStart fFinal fFirst fChain fLast fActive
  have fShared : naturalCfg fStart=prefixCfg pFinal := by
    cases pFinal with
    | mk point memory contents =>
      change point=some .done at pActive
      subst point
      change (⟨some (.natural 0),fieldIso C ((fieldIso C).symm (alphaIso C memory)),
        StackIso.slots naturalRoles (StackIso.slots naturalRoles.symm contents)⟩ : State C)=_
      rw [Equiv.apply_symm_apply]
      congr 1
      funext slot
      fin_cases slot <;> rfl
  let fieldSegment : Segment caller (prefixCfg pFinal) (naturalCfg fFinal)
      (3*(PSTRTMNatValue017.rawPayload (lastNatural input contract)).length+6):=
    ⟨fRun.map naturalCfg,fPath.1.trans (congrArg some fShared),fPath.2.1,fPath.2.2,
      by rw [List.length_map,fTime]⟩
  let whole:=((headerSegment.append toolsSegment).append prefixSegment).append fieldSegment
  have fBank : (naturalCfg fFinal).stk=Function.update pFinal.stk 14
      (NatField.packet (lastNatural input contract) (pFinal.stk 14)) := by
    change StackIso.slots naturalRoles fFinal.stk=_
    rw [fContents]
    funext slot
    fin_cases slot <;> rfl
  have originalFrame : ∀ slot,slot≠0→slot≠1→pFinal.stk slot=background slot := by
    intro slot notZero notOne
    exact ((pFrames pFinal (List.mem_of_getLast? pLast)).2 slot notZero notOne).trans
      (((aFrames aFinal (List.mem_of_getLast? aLast)).2 slot notZero notOne).trans
        ((hFrames hFinal (List.mem_of_getLast? hLast)).2 slot notZero notOne))
  refine ⟨whole.trace,naturalCfg fFinal,suffix,whole.first,whole.chain,whole.last,?_,?_,?_,?_,whole.count⟩
  · change Option.map naturalLabel fFinal.l=some (.rational .boot)
    rw [fActive]; rfl
  · rw [fBank]
    change NatField.packet (lastNatural input contract) (pFinal.stk 14)=_
    rw [originalFrame 14 (by decide) (by decide)]
  · rw [fBank]
    change NatPrefix.tape pFinal.stk=_
    simpa only [List.append_assoc] using pTape
  · intro slot notZero notOne notNatural
    rw [fBank,Function.update_of_ne notNatural]
    exact originalFrame slot notZero notOne

end RootB234.PrepEntry.FirstRaw
