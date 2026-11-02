module

public import RootB234_PrepEntry_RestoreCode_013

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.Restore

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*} {I : Instance}

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

def outputBank (bits : List Bool) (stages tools : Nat) : RatInput.Stack → List Bool :=
  fun slot => if slot=0 then bits else if slot=8 then NatField.packet stages []
    else if slot=9 then NatField.packet tools [] else []

/-- Paid physical0→reverse backup2, actual N8/J9 parse/export, and real
clear0/clear1/reverse2→0 restoration. No original bit is host reloaded. -/
theorem actual (caller : Statement C) (context : C) (input : StatisticalInput I)
    (contract : Contract I) (budget : Rat) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (entry context (preparationInput input contract budget)) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some .done ∧
      final.stk=outputBank (preparationInput input contract budget) I.stageCount I.toolCount ∧
      trace.length≤262144*((preparationInput input contract budget).length+1)^2 := by
  let bits:=preparationInput input contract budget
  let empty : RatInput.Stack → List Bool:=fun _ => []
  let archiveContext : NJ.Store C:=(((context,default),default),default)
  let copyMemory : WholeCopy.Store (NJ.Store C):=(archiveContext,false,false)
  let cFinal:=WholeCopy.state empty .done (archiveContext,true,true) bits (bits.reverse++[]) []
  obtain ⟨cRun,cFirst,cChain,cLast,cCount⟩:=WholeCopy.actual .halt empty copyMemory bits [] []
  have cPath:=copy_path caller cRun _ cFinal cFirst cChain cLast rfl
  have cStart : copyCfg (WholeCopy.state empty .boot copyMemory bits [] [])=entry context bits := by
    change (⟨some (.copy .boot),_,_⟩ : State C)=⟨some (.copy .boot),_,_⟩
    congr 1
    funext slot
    fin_cases slot <;> rfl
  let copyContext : WholeCopy.Store C:=(context,true,true)
  obtain ⟨hRun,hFinal,hFacts⟩:=NJ.actual_polynomial copyContext input contract budget
  let framed : NJ.State (WholeCopy.Store C) → NJ.State (WholeCopy.Store C):=Frame.configuration 2 bits.reverse
  let pRun:=hRun.map framed
  let pFinal:=framed hFinal
  let pBefore:=framed (NJ.entry copyContext bits)
  have pFirst : pRun.head?=some pBefore := by
    rw [List.head?_map,hFacts.first,Option.map_some]
  have pChain : pRun.IsChain (fun a b => TM2.step (NJ.program .halt) a=some b) :=
    Frame.chain_configuration NJ.Work 2 (by decide) bits.reverse (NJ.program .halt) NJ.program_accesses hRun hFacts.chain
  have pLast : pRun.getLast?=some pFinal := by
    rw [List.getLast?_map,hFacts.last,Option.map_some]
  have pActive : pFinal.l=some .done:=hFacts.active
  have pPath:=prep_path caller pRun pBefore pFinal pFirst pChain pLast pActive
  have cPrep : prepCfg pBefore=copyCfg cFinal := by
    change (⟨some (.prep default),_,_⟩ : State C)=⟨some (.prep default),_,_⟩
    congr 1
    funext slot
    change Function.update (NJ.entry copyContext bits).stk 2 bits.reverse slot=
      WholeCopy.bank empty bits (bits.reverse++[]) [] slot
    rw [List.append_nil]
    fin_cases slot <;> rfl
  have cap0 : (pFinal.stk 0).length≤NJ.coefficient*(bits.length+1)^2 := by
    exact (hFacts.boundaries hFinal (List.mem_of_getLast? hFacts.last)).2.1 0
  have cap1 : (pFinal.stk 1).length≤NJ.coefficient*(bits.length+1)^2 := by
    exact (hFacts.boundaries hFinal (List.mem_of_getLast? hFacts.last)).2.1 1
  have cacheN : pFinal.stk 8=NatField.packet I.stageCount []:=hFacts.packetN
  have cacheJ : pFinal.stk 9=NatField.packet I.toolCount []:=hFacts.packetJ
  have other : ∀ slot,slot≠0→slot≠1→slot≠8→slot≠9→pFinal.stk slot=if slot=2 then bits.reverse else [] := by
    intro slot n0 n1 n8 n9
    by_cases n2 : slot=2
    · subst slot
      rfl
    have physical : pFinal.stk slot=hFinal.stk slot:=Function.update_of_ne n2 _ _
    rw [physical]
    simp only [n2,ite_false]
    by_cases n7 : slot=7
    · subst slot
      exact hFacts.scratch
    · exact hFacts.free slot n0 n1 n7 n8 n9
  have backup : pFinal.stk 2=bits.reverse := other 2 (by decide) (by decide) (by decide) (by decide)
  let rewindMemory:=(copyIso C).symm pFinal.var
  let rBefore:=Rewind.state pFinal.stk default rewindMemory (pFinal.stk 0) (pFinal.stk 1) (pFinal.stk 2)
  let rFinal:=Rewind.state pFinal.stk .done (rewindMemory.1,false,false) (pFinal.stk 2).reverse [] []
  obtain ⟨rRun,rFirst,rChain,rLast,rCount⟩:=Rewind.actual .halt pFinal.stk rewindMemory
    (pFinal.stk 0) (pFinal.stk 1) (pFinal.stk 2)
  have rPath:=rewind_path caller rRun rBefore rFinal rFirst rChain rLast rfl
  have pRewind : rewindCfg rBefore=prepCfg pFinal := by
    rcases pFinal with ⟨position,memory,contents⟩
    change position=some NJ.Label.done at pActive
    subst position
    change (⟨some (.rewind default),copyIso C ((copyIso C).symm memory),_⟩ : State C)=
      ⟨some (.rewind default),memory,contents⟩
    rw [Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot <;> rfl
  have rBank : (rewindCfg rFinal).stk=outputBank bits I.stageCount I.toolCount := by
    funext slot
    change Rewind.bank pFinal.stk (pFinal.stk 2).reverse [] [] slot=_
    by_cases n0 : slot=0
    · subst slot
      change (pFinal.stk 2).reverse=bits
      rw [backup,List.reverse_reverse]
    by_cases n1 : slot=1
    · subst slot
      rfl
    by_cases n2 : slot=2
    · subst slot
      rfl
    by_cases n8 : slot=8
    · subst slot
      exact cacheN
    by_cases n9 : slot=9
    · subst slot
      exact cacheJ
    simp only [Rewind.bank,outputBank,n0,n1,n2,n8,n9,ite_false]
    simpa only [n2,ite_false] using other slot n0 n1 n8 n9
  let front : Segment caller (entry context bits) (copyCfg cFinal) (2*bits.length+4):=
    ⟨cRun.map copyCfg,cPath.1.trans (congrArg some cStart),cPath.2.1,cPath.2.2,
      by simpa only [List.length_map] using Nat.le_of_eq cCount⟩
  let middle : Segment caller (copyCfg cFinal) (prepCfg pFinal) (NJ.coefficient*(bits.length+1)^2):=
    ⟨pRun.map prepCfg,pPath.1.trans (congrArg some cPrep),pPath.2.1,pPath.2.2,
      by simpa only [List.length_map,pRun] using hFacts.time⟩
  let back : Segment caller (prepCfg pFinal) (rewindCfg rFinal)
      ((pFinal.stk 0).length+(pFinal.stk 1).length+(pFinal.stk 2).length+4):=
    ⟨rRun.map rewindCfg,rPath.1.trans (congrArg some pRewind),rPath.2.1,rPath.2.2,
      by simpa only [List.length_map] using Nat.le_of_eq rCount⟩
  let whole:=(front.append middle).append back
  have rewound : (pFinal.stk 0).length+(pFinal.stk 1).length+(pFinal.stk 2).length+4≤
      2*NJ.coefficient*(bits.length+1)^2+bits.length+4 := by
    rw [backup,List.length_reverse]
    nlinarith only [cap0,cap1]
  refine ⟨whole.trace,rewindCfg rFinal,whole.head,whole.chain,whole.last,rfl,rBank,?_⟩
  have count:=whole.count
  have base : 1≤bits.length+1 := by omega
  have positive : 1≤(bits.length+1)^2:=Nat.pow_le_pow_left base 2
  have linear : bits.length+1≤(bits.length+1)^2 := by nlinarith only [base]
  dsimp only [NJ.coefficient] at count rewound
  change whole.trace.length≤262144*(bits.length+1)^2
  nlinarith only [count,rewound,positive,linear]

end RootB234.PrepEntry.Restore
