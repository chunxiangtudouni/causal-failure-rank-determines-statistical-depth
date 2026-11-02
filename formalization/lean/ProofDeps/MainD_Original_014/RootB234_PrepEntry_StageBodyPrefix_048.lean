module

public import RootB234_PrepEntry_StageFrontCode_047

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

def bodyPrefixTime (input : StatisticalInput I) (contract : Contract I) : Nat :=
  ((PSTRTMNatValue017.rawPayload I.toolCount).length^2+9*(PSTRTMNatValue017.rawPayload I.toolCount).length+5)+
  NatPrefix.workTime (firstNumbers input contract)+
  (3*(PSTRTMNatValue017.rawPayload (lastNatural input contract)).length+6)

/-- Actual continuation from a real header boundary. Its native memory
is the caller's current allocation; the saved header Bool is preserved. -/
theorem actual_body_prefix (caller : Statement C) (before : State C)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat)
    (active : before.l=some (.tools 0)) (control : before.var.1.1.2.1=0)
    (physical : NatPrefix.tape before.stk=Tape.mk₂
      (fieldLeft [] (preparationData input contract budget).length I.stageCount)
      (false::(encodeNat I.toolCount++NJ.afterTools input contract budget))) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some before ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some (.rational .boot) ∧
      final.stk 14=NatField.packet (lastNatural input contract) (before.stk 14) ∧
      NatPrefix.tape final.stk=Tape.mk₂
        (NatPrefix.archived (NJ.finalLeft input contract budget) (firstNumbers input contract))
        (encodeDatum (.rational (firstValue input budget))++wireSuffix input contract budget++[true]) ∧
      (∀ slot,slot≠0→slot≠1→slot≠14→final.stk slot=before.stk slot) ∧
      trace.length≤bodyPrefixTime input contract ∧ final.var.2=before.var.2 := by
  let aStart : Alpha.State (HeaderNat.Store (C × RawGetter.ParserMemory)):=
    ⟨some 0,(alphaIso C).symm before.var,before.stk⟩
  have aControl : aStart.var.2.1=0 := control
  have aPhysical : NatPrefix.tape before.stk=Tape.mk₂
      (fieldLeft [] (preparationData input contract budget).length I.stageCount)
      (false::(encodeNat I.toolCount++NJ.afterTools input contract budget)) := physical
  obtain ⟨aRun,aFinal,aFirst,aChain,aLast,aActive,aTape,aTime,aContext,aFrames⟩:=
    Alpha.actual aStart.var.1 aStart.var.2 before.stk _ I.toolCount _ aControl aPhysical
  have aPath:=tools_path caller aRun aStart aFinal aFirst aChain aLast aActive
  have aShared : toolsCfg aStart=before := by
    cases before with
    | mk point memory contents =>
      change point=some (.tools 0) at active
      subst point
      change (⟨some (.tools 0),alphaIso C ((alphaIso C).symm memory),contents⟩ : State C)=_
      rw [Equiv.apply_symm_apply]
  let toolsSegment : Segment caller before (toolsCfg aFinal)
      ((PSTRTMNatValue017.rawPayload I.toolCount).length^2+9*(PSTRTMNatValue017.rawPayload I.toolCount).length+5):=
    ⟨aRun.map toolsCfg,aPath.1.trans (congrArg some aShared),aPath.2.1,aPath.2.2,by
      rw [List.length_map,aTime]⟩
  let suffix:=wireSuffix input contract budget
  have stream:=afterTools_exact input contract budget
  let pStart : NatPrefix.State (HeaderNat.Store (C × RawGetter.ParserMemory)):=
    ⟨some .check,aFinal.var,aFinal.stk⟩
  have pPhysical : NatPrefix.tape aFinal.stk=Tape.mk₂ (NJ.finalLeft input contract budget)
      (NatPrefix.naturals (firstNumbers input contract)++
        encodeDatum (.rational (firstValue input budget))++(suffix++[true])) := by
    rw [show NatPrefix.tape aFinal.stk=_ from aTape,stream]
    simp only [List.append_assoc]
    rfl
  obtain ⟨pRun,pFinal,pFirst,pChain,pLast,pActive,pTape,pContext,pTime,pFrames⟩:=
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
  obtain ⟨fRun,fFinal,fFirst,fChain,fLast,fActive,fContext,fContents,fTime⟩:=
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
  let whole:=(toolsSegment.append prefixSegment).append fieldSegment
  have fBank : (naturalCfg fFinal).stk=Function.update pFinal.stk 14
      (NatField.packet (lastNatural input contract) (pFinal.stk 14)) := by
    change StackIso.slots naturalRoles fFinal.stk=_
    rw [fContents]
    funext slot
    fin_cases slot <;> rfl
  have originalFrame : ∀ slot,slot≠0→slot≠1→pFinal.stk slot=before.stk slot := by
    intro slot notZero notOne
    exact ((pFrames pFinal (List.mem_of_getLast? pLast)).2 slot notZero notOne).trans
      ((aFrames aFinal (List.mem_of_getLast? aLast)).2 slot notZero notOne)
  refine ⟨whole.trace,naturalCfg fFinal,whole.first,whole.chain,whole.last,?_,?_,?_,?_,whole.count,?_⟩
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

  · have alphaHeader : (toolsCfg aFinal).var.2=before.var.2 := by
      exact congrArg (fun memory : HeaderNat.Store (C × RawGetter.ParserMemory) => memory.2) aContext
    have prefixHeader : (prefixCfg pFinal).var.2=(toolsCfg aFinal).var.2 := by
      exact congrArg (fun memory : HeaderNat.Store (C × RawGetter.ParserMemory) => memory.2) pContext
    have fieldHeader : (naturalCfg fFinal).var.2=(prefixCfg pFinal).var.2 := by
      exact congrArg (fun memory : FieldContext C => memory.2) fContext
    exact fieldHeader.trans (prefixHeader.trans alphaHeader)

end RootB234.PrepEntry.FirstRaw
