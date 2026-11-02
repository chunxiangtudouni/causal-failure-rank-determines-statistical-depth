module

public import RootB234_PrepEntry_NJCode_007

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.NJ

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep PSTRTMWordPreparationFront214

variable {C : Type*} {I : Instance}

def afterTools (input : StatisticalInput I) (contract : Contract I) (budget : Rat) : List Bool :=
  ((preparationData input contract budget).drop 2).flatMap encodeDatum ++ [true]

theorem preparationTail_tools (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    preparationTail input contract budget=false::(encodeNat I.toolCount++afterTools input contract budget) := by
  change (false::encodeNat I.toolCount)++((preparationData input contract budget).drop 2).flatMap encodeDatum++[true]=_
  simp only [afterTools,List.cons_append,List.append_assoc]

def finalLeft (input : StatisticalInput I) (contract : Contract I) (budget : Rat) : List Bool :=
  Alpha.nextLeft (fieldLeft [] (preparationData input contract budget).length I.stageCount) I.toolCount

/-- Original literal preparation input is the only data. First N is actually
exported on8, then the next original natural J is parsed/exported on9. All
finite blocks are allocated at entry; every join is exact whole state. -/
theorem actual (caller : Statement C) (context : C) (input : StatisticalInput I)
    (contract : Contract I) (budget : Rat) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (entry context (preparationInput input contract budget)) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some .done ∧
      final.stk 8=NatField.packet I.stageCount [] ∧ final.stk 9=NatField.packet I.toolCount [] ∧
      final.stk 7=[] ∧
      Tape.mk' (ListBlank.mk (final.stk 1)) (ListBlank.mk (final.stk 0))=Tape.mk₂
        (finalLeft input contract budget) (afterTools input contract budget) ∧
      (∀ slot,slot≠0→slot≠1→slot≠7→slot≠8→slot≠9→final.stk slot=[]) ∧
      trace.length≤64*((preparationInput input contract budget).length+1)^2 := by
  obtain ⟨nRun,nFinal,_nParsed,nFirst,nChain,nLast,_nMember,nActive,nContext,nPacket,nScratch,nTape,nFree,nTime⟩:=
    RootB234.PrepEntry.actual .halt (context,(default : Alpha.NativeMemory)) default (fun _ => [])
      input contract budget
  have nPath:=stages_path caller nRun _ nFinal nFirst nChain nLast nActive
  let aStart:=alphaStart nFinal
  have aControl : aStart.var.2.1=0 := by
    have saved:=congrArg Prod.snd nContext
    change nFinal.var.1.1.2=default at saved
    change nFinal.var.1.1.2.1=0
    rw [saved]
    rfl
  have aTape : Tape.mk' (ListBlank.mk (nFinal.stk 1)) (ListBlank.mk (nFinal.stk 0))=Tape.mk₂
      (fieldLeft [] (preparationData input contract budget).length I.stageCount)
      (false::(encodeNat I.toolCount++afterTools input contract budget)) := by
    rw [nTape,preparationTail_tools]
  obtain ⟨aRun,aFinal,aFirst,aChain,aLast,aActive,aFinalTape,aTime,_aContext,aFrames⟩:=
    Alpha.actual aStart.var.1 aStart.var.2 nFinal.stk _ I.toolCount _ aControl aTape
  have aPath:=alpha_path caller aRun aStart aFinal aFirst aChain aLast aActive
  have aHead : (aRun.map alphaCfg).head?=some (stagesCfg nFinal) :=
    aPath.1.trans (congrArg some (alpha_shared nFinal nActive))
  have aShape : stagesCfg nFinal::(aRun.map alphaCfg).tail=aRun.map alphaCfg := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp aHead
    rw [same]
    rfl
  let firstRun:=nRun.map stagesCfg++(aRun.map alphaCfg).tail
  have firstFirst : firstRun.head?=some (entry context (preparationInput input contract budget)) := by
    rw [List.head?_append,nPath.1]
    rfl
  have firstChain : firstRun.IsChain (fun a b => TM2.step (program caller) a=some b) :=
    NativeTrace.join_chain _ _ _ nPath.2.2 nPath.2.1 (aShape.symm ▸ aPath.2.1)
  have firstLast : firstRun.getLast?=some (alphaCfg aFinal) :=
    (NativeTrace.join_last _ _ _ nPath.2.2).trans (aShape.symm ▸ aPath.2.2)
  have wholeLeft:=congrArg Tape.left aFinalTape
  change ListBlank.mk (aFinal.stk 1)=ListBlank.mk
    (fieldLeft (false::headerLeft [] (preparationData input contract budget).length) I.stageCount I.toolCount) at wholeLeft
  have physical:=Alpha.finite_archive_tail (false::headerLeft [] (preparationData input contract budget).length)
    I.stageCount I.toolCount aFinal.stk wholeLeft
  let fStart:=fieldStart aFinal
  have fPhysical : ∃ left,fStart.stk 1=false::
      (PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload I.toolCount).reverse++false::left) := by
    change ∃ left,aFinal.stk 1=_
    exact physical
  obtain ⟨fRun,fFinal,fFirst,fChain,fLast,fActive,_fContext,fContents,fTime⟩:=
    NatField.actual_current fStart.var fStart.stk I.toolCount fPhysical
  have fPath:=field_path caller fRun fStart fFinal fFirst fChain fLast fActive
  have fHead : (fRun.map fieldCfg).head?=some (alphaCfg aFinal) :=
    fPath.1.trans (congrArg some (field_shared aFinal aActive))
  have fShape : alphaCfg aFinal::(fRun.map fieldCfg).tail=fRun.map fieldCfg := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp fHead
    rw [same]
    rfl
  let trace:=firstRun++(fRun.map fieldCfg).tail
  have first : trace.head?=some (entry context (preparationInput input contract budget)) := by
    rw [List.head?_append,firstFirst]
    rfl
  have chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b) :=
    NativeTrace.join_chain _ _ _ firstLast firstChain (fShape.symm ▸ fPath.2.1)
  have last : trace.getLast?=some (fieldCfg fFinal) :=
    (NativeTrace.join_last _ _ _ firstLast).trans (fShape.symm ▸ fPath.2.2)
  have contents : (fieldCfg fFinal).stk=Function.update aFinal.stk 9
      (NatField.packet I.toolCount (aFinal.stk 9)) := by
    change StackIso.slots roles fFinal.stk=_
    rw [fContents]
    funext slot
    fin_cases slot <;> rfl
  have fields : ∀ slot,slot≠9→(fieldCfg fFinal).stk slot=aFinal.stk slot := by
    intro slot different
    rw [contents]
    exact Function.update_of_ne different _ _
  have aFrame:=aFrames aFinal (List.mem_of_getLast? aLast)
  have widthBound : (PSTRTMNatValue017.rawPayload I.toolCount).length≤(preparationInput input contract budget).length := by
    rw [preparation_input,preparationTail_tools]
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn,List.length_append,List.length_cons,
      PSTRTMLength004.encodeNat_length]
    omega
  have widthSquared:=Nat.pow_le_pow_left widthBound 2
  have base : 1≤(preparationInput input contract budget).length+1 := by omega
  have positive : 1≤((preparationInput input contract budget).length+1)^2:=Nat.pow_le_pow_left base 2
  have linear : (preparationInput input contract budget).length+1≤((preparationInput input contract budget).length+1)^2 := by nlinarith only [base]
  have count : trace.length≤32*((preparationInput input contract budget).length+1)^2+
      ((PSTRTMNatValue017.rawPayload I.toolCount).length^2+9*(PSTRTMNatValue017.rawPayload I.toolCount).length+5)+
      (3*(PSTRTMNatValue017.rawPayload I.toolCount).length+6) := by
    dsimp only [trace,firstRun]
    simp only [List.length_append,List.length_map,List.length_tail]
    omega
  refine ⟨trace,fieldCfg fFinal,first,chain,last,?_,?_,?_,?_,?_,?_,?_⟩
  · change fFinal.l.map fieldLabel=some .done
    rw [fActive]
    rfl
  · exact (fields 8 (by decide)).trans ((aFrame.2 8 (by decide) (by decide)).trans nPacket)
  · rw [contents,Function.update_self,aFrame.2 9 (by decide) (by decide),nFree 9 (by decide) (by decide) (by decide) (by decide)]
  · exact (fields 7 (by decide)).trans ((aFrame.2 7 (by decide) (by decide)).trans nScratch)
  · rw [fields 1 (by decide),fields 0 (by decide)]
    exact aFinalTape
  · intro slot n0 n1 n7 n8 n9
    exact (fields slot n9).trans ((aFrame.2 slot n0 n1).trans (nFree slot n0 n1 n7 n8))
  · nlinarith only [count,widthBound,widthSquared,positive,linear]

end RootB234.PrepEntry.NJ
