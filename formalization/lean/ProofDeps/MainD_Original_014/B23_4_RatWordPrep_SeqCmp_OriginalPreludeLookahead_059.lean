module

public import B23_4_RatWordPrep_SeqCmp_OriginalPreludePaths_058
public import B23_4_RatWordPrep_SeqCmp_HeaderNatWorkspace_058a

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.OriginalPrelude

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

variable {C : Type*}

structure Segment (caller : Statement C) (before final : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final
  count : trace.length ≤ budget

def Segment.append {caller : Statement C} {before middle final : State C} {A B : Nat}
    (front : Segment caller before middle A) (back : Segment caller middle final B) :
    Segment caller before final (A+B) := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.head
    rw [same]
    rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.head]
    rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have a:=front.count
    have b:=back.count
    simp only [List.length_append,List.length_tail]
    omega

/-- A real prefix of the four-stage source. Runtime alphabet cache8 has
been produced,0 has been restored from physical2,1/2 cleared, and the fee
component's PREALLOCATED register block is still its actual initial block. -/
theorem actual_lookahead (caller : Statement C) (context : C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (run : List (State C)) (final : State C),
      run.head?=some (entry context (wordInput E target word)) ∧
      run.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      run.getLast?=some final ∧ final.l=some (.fee default) ∧
      feeMemory final.var=initialFeeMemory context ∧
      final.stk=Function.update (OriginalFee.entry (rawMemory context) default default (wordInput E target word)).stk 8
        (NatField.packet E.alphabetSize []) ∧
      run.length ≤ 2048*((wordInput E target word).length+1)^2 := by
  let bits:=wordInput E target word
  let empty : RatInput.Stack → List Bool:=fun _ => []
  let archiveContext : HeaderNat.Store (OriginalFee.Store C):=((initialFeeMemory context,default),default)
  let copyMemory : WholeCopy.Store (HeaderNat.Store (OriginalFee.Store C)):=(archiveContext,false,false)
  let cFinal:=WholeCopy.state empty .done (archiveContext,true,true) bits (bits.reverse++[]) []
  obtain ⟨cRun,cFirst,cChain,cLast,cCount⟩:=WholeCopy.actual .halt empty copyMemory bits [] []
  have cPath:=copy_path caller cRun _ cFinal cFirst cChain cLast rfl
  have cStart : copyCfg (WholeCopy.state empty .boot copyMemory bits [] [])=entry context bits := by
    change (⟨some (.copy .boot),_,_⟩ : State C)=⟨some (.copy .boot),_,_⟩
    congr 1
    funext slot
    fin_cases slot <;> rfl
  let copyContext : WholeCopy.Store (OriginalFee.Store C):=(initialFeeMemory context,true,true)
  obtain ⟨hRun,hFinal,_hParsed,hFirst,hChain,hLast,_hMember,hActive,hContext,hCache,hScratch,_hTape,hFrame,hTime⟩:=
    HeaderNat.actual .halt copyContext default cFinal.stk E target word
  have hPath:=header_path caller hRun _ hFinal hFirst hChain hLast hActive
  have hTimeBits : hRun.length ≤ 32*(bits.length+1)^2 := hTime
  have cHeader : headerCfg (HeaderNat.entry copyContext default cFinal.stk bits)=copyCfg cFinal := by
    change (⟨some (.header default),_,_⟩ : State C)=⟨some (.header default),_,_⟩
    congr 1
    funext slot
    fin_cases slot <;> rfl
  have initialBound : ∀ slot,((HeaderNat.entry copyContext default cFinal.stk bits).stk slot).length ≤ bits.length := by
    intro slot
    have same:=congrArg (fun current : State C => current.stk slot) cHeader
    change (HeaderNat.entry copyContext default cFinal.stk bits).stk slot=cFinal.stk slot at same
    rw [same]
    change (WholeCopy.bank empty bits (bits.reverse++[]) [] slot).length ≤ bits.length
    fin_cases slot <;> simp [WholeCopy.bank,empty,List.length_reverse]
  have hBounds:=HeaderNat.trace_bound hRun _ bits.length hFirst hChain initialBound
  have cap0 : (hFinal.stk 0).length ≤ bits.length+512*(bits.length+1)^2 := by
    have small:=hBounds hFinal (List.mem_of_getLast? hLast) 0
    omega
  have cap1 : (hFinal.stk 1).length ≤ bits.length+512*(bits.length+1)^2 := by
    have small:=hBounds hFinal (List.mem_of_getLast? hLast) 1
    omega
  have cache : hFinal.stk 8=NatField.packet E.alphabetSize [] := hCache
  have stored : hFinal.var.1.1.1=initialFeeMemory context :=
    congrArg (fun memory : WholeCopy.Store (OriginalFee.Store C) => memory.1) hContext
  have other : ∀ slot,slot≠0→slot≠1→slot≠8→hFinal.stk slot=if slot=2 then bits.reverse else [] := by
    intro slot n0 n1 n8
    by_cases n7 : slot=7
    · subst slot
      exact hScratch
    · rw [hFrame slot n0 n1 n7 n8]
      change WholeCopy.bank empty bits (bits.reverse++[]) [] slot=_
      simp only [WholeCopy.bank,empty,n0,ite_false,ite_self,List.append_nil]
  have backup : hFinal.stk 2=bits.reverse := other 2 (by decide) (by decide) (by decide)
  let rewindMemory:=(copyIso C).symm hFinal.var
  let rBefore:=Rewind.state hFinal.stk default rewindMemory (hFinal.stk 0) (hFinal.stk 1) (hFinal.stk 2)
  let rFinal:=Rewind.state hFinal.stk .done (rewindMemory.1,false,false) (hFinal.stk 2).reverse [] []
  obtain ⟨rRun,rFirst,rChain,rLast,rCount⟩:=Rewind.actual .halt hFinal.stk rewindMemory
    (hFinal.stk 0) (hFinal.stk 1) (hFinal.stk 2)
  have rPath:=rewind_path caller rRun rBefore rFinal rFirst rChain rLast rfl
  have hRewind : rewindCfg rBefore=headerCfg hFinal := by
    rcases hFinal with ⟨position,memory,contents⟩
    change position=some HeaderNat.Label.done at hActive
    subst position
    change (⟨some (.rewind default),copyIso C ((copyIso C).symm memory),_⟩ : State C)=
      ⟨some (.rewind default),memory,contents⟩
    rw [Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot <;> rfl
  have rStored : feeMemory (rewindCfg rFinal).var=initialFeeMemory context := by
    change hFinal.var.1.1.1=initialFeeMemory context
    exact stored
  have rBank : (rewindCfg rFinal).stk=Function.update
      (OriginalFee.entry (rawMemory context) default default bits).stk 8 (NatField.packet E.alphabetSize []) := by
    funext slot
    change Rewind.bank hFinal.stk (hFinal.stk 2).reverse [] [] slot=_
    rw [OriginalFee.entry_slots]
    by_cases n0 : slot=0
    · subst slot
      change (hFinal.stk 2).reverse=bits
      rw [backup,List.reverse_reverse]
    by_cases n1 : slot=1
    · subst slot
      rfl
    by_cases n2 : slot=2
    · subst slot
      rfl
    by_cases n8 : slot=8
    · subst slot
      change hFinal.stk 8=NatField.packet E.alphabetSize []
      exact cache
    simp only [Rewind.bank,n0,n1,n2,ite_false,Function.update_of_ne n8]
    simpa only [n2,ite_false] using other slot n0 n1 n8
  let front : Segment caller (entry context bits) (copyCfg cFinal) (2*bits.length+4):=
    ⟨cRun.map copyCfg,cPath.1.trans (congrArg some cStart),cPath.2.1,cPath.2.2,
      by simpa only [List.length_map] using Nat.le_of_eq cCount⟩
  let middle : Segment caller (copyCfg cFinal) (headerCfg hFinal) (32*(bits.length+1)^2):=
    ⟨hRun.map headerCfg,hPath.1.trans (congrArg some cHeader),hPath.2.1,hPath.2.2,
      by simpa only [List.length_map] using hTime⟩
  let back : Segment caller (headerCfg hFinal) (rewindCfg rFinal)
      ((hFinal.stk 0).length+(hFinal.stk 1).length+(hFinal.stk 2).length+4):=
    ⟨rRun.map rewindCfg,rPath.1.trans (congrArg some hRewind),rPath.2.1,rPath.2.2,
      by simpa only [List.length_map] using Nat.le_of_eq rCount⟩
  let whole:=(front.append middle).append back
  have rewound : (hFinal.stk 0).length+(hFinal.stk 1).length+(hFinal.stk 2).length+4 ≤
      3*bits.length+1024*(bits.length+1)^2+4 := by
    rw [backup,List.length_reverse]
    omega
  refine ⟨whole.trace,rewindCfg rFinal,whole.head,whole.chain,whole.last,rfl,rStored,rBank,?_⟩
  have count:=whole.count
  have base : 1 ≤ bits.length+1 := by omega
  have positive : 1 ≤ (bits.length+1)^2 := Nat.pow_le_pow_left base 2
  have linear : bits.length+1 ≤ (bits.length+1)^2 := by nlinarith
  change whole.trace.length ≤ 2048*(bits.length+1)^2
  nlinarith only [count,rewound,positive,linear]

end B23_4_RatWordPrep.OriginalPrelude
