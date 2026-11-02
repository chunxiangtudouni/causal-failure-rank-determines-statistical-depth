module

public import B23_4_RatWordPrep_SeqCmp_HeaderNatCode_053

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.HeaderNat

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRTMWordFrontCode213 PSTRTMWordPreparationFront214

variable {C : Type*}

/-- ORIGINAL wordInput -> actual canonical alphabet Nat packet on8.
The packet is copied from the real header archive, never host loaded. -/
theorem actual (caller : Statement C) (context : C) (flags : PSTRSymbolicNaturalExport.Store)
    (background : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (run : List (State C)) (final parsed : State C),
      run.head?=some (entry context flags background (wordInput E target word)) ∧
      run.IsChain (fun before after => TM2.step (program caller) before=some after) ∧
      run.getLast?=some final ∧ parsed∈run ∧ final.l=some .done ∧ final.var.1.1=context ∧
      final.stk 8=NatField.packet E.alphabetSize (background 8) ∧ final.stk 7=background 7 ∧
      Tape.mk' (ListBlank.mk (final.stk 1)) (ListBlank.mk (final.stk 0))=Tape.mk₂
        (fieldLeft [] (wordData E target word).length E.alphabetSize) (wordTail E target word) ∧
      (∀ slot,slot≠0→slot≠1→slot≠7→slot≠8→final.stk slot=background slot) ∧
      run.length ≤ 32*((wordInput E target word).length+1)^2 := by
  obtain ⟨hRun,hFinal,hFirst,hChain,hLast,hActive,hTape,hTime,hFrames,_hMass⟩:=
    Header.actual (context,flags) background E target word
  have hPath:=header_path caller hRun _ hFinal hFirst hChain hLast hActive
  have wholeLeft:=congrArg Tape.left hTape
  change ListBlank.mk (hFinal.stk 1)=ListBlank.mk
    (fieldLeft [] (wordData E target word).length E.alphabetSize) at wholeLeft
  have physical:=Header.finite_archive (wordData E target word).length E.alphabetSize hFinal.stk wholeLeft
  let smallBank:=StackIso.slots roles.symm hFinal.stk
  let smallMemory:=(fieldIso C).symm hFinal.var
  have smallPhysical : ∃ left,smallBank 1=false::
      (PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload E.alphabetSize).reverse++false::left) := by
    change ∃ left,hFinal.stk 1=_
    exact physical
  obtain ⟨eRun,eFinal,eFirst,eChain,eLast,eActive,eContext,eContents,eTime⟩:=
    NatField.actual_current smallMemory smallBank E.alphabetSize smallPhysical
  have ePath:=field_path caller eRun _ eFinal eFirst eChain eLast eActive
  have sharedHead : (eRun.map fieldCfg).head?=some (headerCfg hFinal) :=
    ePath.1.trans (congrArg some (shared hFinal hActive))
  have shape : headerCfg hFinal::(eRun.map fieldCfg).tail=eRun.map fieldCfg := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp sharedHead
    rw [same]
    rfl
  let run:=hRun.map headerCfg++(eRun.map fieldCfg).tail
  have first : run.head?=some (entry context flags background (wordInput E target word)) := by
    rw [List.head?_append,hPath.1]
    rfl
  have chain : run.IsChain (fun a b => TM2.step (program caller) a=some b) :=
    NativeTrace.join_chain _ _ _ hPath.2.2 hPath.2.1 (shape.symm ▸ ePath.2.1)
  have last : run.getLast?=some (fieldCfg eFinal) :=
    (NativeTrace.join_last _ _ _ hPath.2.2).trans (shape.symm ▸ ePath.2.2)
  have contents : (fieldCfg eFinal).stk=Function.update hFinal.stk 8
      (NatField.packet E.alphabetSize (hFinal.stk 8)) := by
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
  have widthBound : (PSTRTMNatValue017.rawPayload E.alphabetSize).length ≤ (wordInput E target word).length := by
    rw [word_input]
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn,List.length_append,List.length_cons,
      PSTRTMLength004.encodeNat_length]
    omega
  have count : run.length ≤ 16*((wordInput E target word).length+1)^2+1+
      (3*(PSTRTMNatValue017.rawPayload E.alphabetSize).length+6) := by
    dsimp only [run]
    simp only [List.length_append,List.length_map,List.length_tail]
    omega
  have base : 1 ≤ (wordInput E target word).length+1 := by omega
  have positive : 1 ≤ ((wordInput E target word).length+1)^2 := Nat.pow_le_pow_left base 2
  have linear : (wordInput E target word).length+1 ≤ ((wordInput E target word).length+1)^2 := by nlinarith
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

end B23_4_RatWordPrep.HeaderNat
