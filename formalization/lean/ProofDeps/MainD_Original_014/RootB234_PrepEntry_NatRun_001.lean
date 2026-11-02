module

public import B23_4_RatWordPrep_SeqCmp_HeaderNatRun_054

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRTMWordFrontCode213 PSTRTMWordPreparationFront214
open B23_4_RatWordPrep

namespace PrepHeader
open Header

theorem header_actual {C : Type*} (context : C) (background : RatInput.Stack → List Bool)
    {I : Instance} (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ (run : List (State C)) (final : State C),
      run.head?=some (entry context background (preparationInput input contract budget)) ∧
      run.IsChain (fun before after => TM2.step (program .halt) before=some after) ∧
      run.getLast?=some final ∧ final.l=some 1 ∧
      (VirtualBool.representedState final).Tape=Tape.mk₂
        (fieldLeft [] (preparationData input contract budget).length I.stageCount) (preparationTail input contract budget) ∧
      run.length ≤ 16*((preparationInput input contract budget).length+1)^2+1 ∧
      (∀ current∈run,current.var.1=context ∧ ∀ slot,slot≠0→slot≠1→current.stk slot=background slot) ∧
      ∀ current∈run,VirtualReturn.occupiedSlots current.stk ≤ VirtualReturn.outside background+
        64*((preparationInput input contract budget).length+1)^2 := by
  have old:=preparation_front_runs input contract budget
  obtain ⟨run,final,first,chain,last,active,represented,_order,count,_context,frames,mass⟩:=
    VirtualBool.same_old_run frontMachine .halt context background (preparationInput input contract budget)
      (preparationTrace input contract budget) (preparationFinal input contract budget) old.1 old.2.1 old.2.2.1 old.2.2.2.1
  have tape:=congrArg TM0.Cfg.Tape represented
  rw [preparation_front_final_tape] at tape
  have oldSpace : visitedSpace frontMachine (preparationInput input contract budget).length (preparationTrace input contract budget) ≤
      64*((preparationInput input contract budget).length+1)^2 := by
    simpa only [List.take_length] using preparation_front_prefix_space_le input contract budget (preparationTrace input contract budget).length
  refine ⟨run,final,first,chain,last,active,tape,?_,frames,?_⟩
  · rw [count]
    exact Nat.add_le_add_right (preparation_front_time_le input contract budget) 1
  · intro current member
    exact (mass current member).trans (Nat.add_le_add_left oldSpace _)

end PrepHeader

open HeaderNat
open PrepHeader

variable {C : Type*}

theorem actual (caller : Statement C) (context : C) (flags : PSTRSymbolicNaturalExport.Store)
    (background : RatInput.Stack → List Bool) {I : Instance} (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ (run : List (State C)) (final parsed : State C),
      run.head?=some (entry context flags background (preparationInput input contract budget)) ∧
      run.IsChain (fun before after => TM2.step (program caller) before=some after) ∧
      run.getLast?=some final ∧ parsed∈run ∧ final.l=some .done ∧ final.var.1.1=context ∧
      final.stk 8=NatField.packet I.stageCount (background 8) ∧ final.stk 7=background 7 ∧
      Tape.mk' (ListBlank.mk (final.stk 1)) (ListBlank.mk (final.stk 0))=Tape.mk₂
        (fieldLeft [] (preparationData input contract budget).length I.stageCount) (preparationTail input contract budget) ∧
      (∀ slot,slot≠0→slot≠1→slot≠7→slot≠8→final.stk slot=background slot) ∧
      run.length ≤ 32*((preparationInput input contract budget).length+1)^2 := by
  obtain ⟨hRun,hFinal,hFirst,hChain,hLast,hActive,hTape,hTime,hFrames,_hMass⟩:=
    header_actual (context,flags) background input contract budget
  have hPath:=header_path caller hRun _ hFinal hFirst hChain hLast hActive
  have wholeLeft:=congrArg Tape.left hTape
  change ListBlank.mk (hFinal.stk 1)=ListBlank.mk
    (fieldLeft [] (preparationData input contract budget).length I.stageCount) at wholeLeft
  have physical:=Header.finite_archive (preparationData input contract budget).length I.stageCount hFinal.stk wholeLeft
  let smallBank:=StackIso.slots roles.symm hFinal.stk
  let smallMemory:=(fieldIso C).symm hFinal.var
  have smallPhysical : ∃ left,smallBank 1=false::
      (PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload I.stageCount).reverse++false::left) := by
    change ∃ left,hFinal.stk 1=_
    exact physical
  obtain ⟨eRun,eFinal,eFirst,eChain,eLast,eActive,eContext,eContents,eTime⟩:=
    NatField.actual_current smallMemory smallBank I.stageCount smallPhysical
  have ePath:=field_path caller eRun _ eFinal eFirst eChain eLast eActive
  have sharedHead : (eRun.map fieldCfg).head?=some (headerCfg hFinal) :=
    ePath.1.trans (congrArg some (shared hFinal hActive))
  have shape : headerCfg hFinal::(eRun.map fieldCfg).tail=eRun.map fieldCfg := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp sharedHead
    rw [same]
    rfl
  let run:=hRun.map headerCfg++(eRun.map fieldCfg).tail
  have first : run.head?=some (entry context flags background (preparationInput input contract budget)) := by
    rw [List.head?_append,hPath.1]
    rfl
  have chain : run.IsChain (fun a b => TM2.step (program caller) a=some b) :=
    NativeTrace.join_chain _ _ _ hPath.2.2 hPath.2.1 (shape.symm ▸ ePath.2.1)
  have last : run.getLast?=some (fieldCfg eFinal) :=
    (NativeTrace.join_last _ _ _ hPath.2.2).trans (shape.symm ▸ ePath.2.2)
  have contents : (fieldCfg eFinal).stk=Function.update hFinal.stk 8
      (NatField.packet I.stageCount (hFinal.stk 8)) := by
    change StackIso.slots roles eFinal.stk=_
    rw [eContents]
    funext slot
    fin_cases slot <;> rfl
  have fields : ∀ slot,slot≠8→(fieldCfg eFinal).stk slot=hFinal.stk slot := by
    intro slot different
    rw [contents]
    exact Function.update_of_ne different _ _
  have hFinalFrame:=hFrames hFinal (List.mem_of_getLast? hLast)
  have finalContext : (fieldCfg eFinal).var.1.1=context := by
    change eFinal.var.1.1=context
    have readContext:=congrArg (fun memory : Header.Store C => memory.1) eContext
    change eFinal.var.1.1=hFinal.var.1.1 at readContext
    exact readContext.trans (congrArg (fun memory : NatField.Store C => memory.1) hFinalFrame.1)
  have widthBound : (PSTRTMNatValue017.rawPayload I.stageCount).length ≤ (preparationInput input contract budget).length := by
    rw [preparation_input]
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn,List.length_append,List.length_cons,
      PSTRTMLength004.encodeNat_length]
    omega
  have count : run.length ≤ 16*((preparationInput input contract budget).length+1)^2+1+
      (3*(PSTRTMNatValue017.rawPayload I.stageCount).length+6) := by
    dsimp only [run]
    simp only [List.length_append,List.length_map,List.length_tail]
    omega
  have base : 1 ≤ (preparationInput input contract budget).length+1 := by omega
  have positive : 1 ≤ ((preparationInput input contract budget).length+1)^2 := Nat.pow_le_pow_left base 2
  have linear : (preparationInput input contract budget).length+1 ≤ ((preparationInput input contract budget).length+1)^2 := by nlinarith
  refine ⟨run,fieldCfg eFinal,headerCfg hFinal,first,chain,last,?_,?_,finalContext,?_,?_,?_,?_,?_⟩
  · exact List.mem_append_left _ (List.mem_of_getLast? hPath.2.2)
  · change eFinal.l.map fieldLabel=some .done
    rw [eActive]
    rfl
  · rw [contents,Function.update_self,hFinalFrame.2 8 (by decide) (by decide)]
  · exact (fields 7 (by decide)).trans (hFinalFrame.2 7 (by decide) (by decide))
  · rw [fields 1 (by decide),fields 0 (by decide)]
    exact hTape
  · intro slot n0 n1 _n7 n8
    exact (fields slot n8).trans (hFinalFrame.2 slot n0 n1)
  · nlinarith only [count,widthBound,positive,linear]


end RootB234.PrepEntry
