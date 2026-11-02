module

public import RootB234_PrepEntry_BudgetPrefixRun_027

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.Budget

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*} {I : Instance}

def outputBank (bits : List Bool) (stages tools : Nat) (budget : Rat) : RatInput.Stack → List Bool :=
  fun slot => if slot=0 then bits else if slot=8 then NatField.packet stages []
    else if slot=9 then NatField.packet tools [] else if slot=15 then RatInput.Encoder.packet budget [] else []

/-- One fixed source from literal original input to physical N8/J9/budget15
and exact restored original input0. Both copies and both rewinds are paid;
the final return remains ACTIVE and its caller is not executed. -/
theorem actual (context : C) (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (entry context (preparationInput input contract budget)) ∧
      trace.IsChain (fun a b => TM2.step (program .halt) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some .done ∧
      final.stk=outputBank (preparationInput input contract budget) I.stageCount I.toolCount budget ∧
      trace.length≤4294967296*((preparationInput input contract budget).length+1)^3 := by
  let bits:=preparationInput input contract budget
  obtain ⟨pRun,pFinal,pFacts⟩:=actual_prefix context input contract budget
  have backup : pFinal.stk 2=bits.reverse:=pFacts.backup
  let rewindMemory:=(Restore.copyIso (C × RawNative.NativeMemory)).symm pFinal.var
  let rBefore:=Rewind.state pFinal.stk default rewindMemory (pFinal.stk 0) (pFinal.stk 1) (pFinal.stk 2)
  let rFinal:=Rewind.state pFinal.stk .done (rewindMemory.1,false,false) (pFinal.stk 2).reverse [] []
  obtain ⟨rRun,rFirst,rChain,rLast,rTime⟩:=Rewind.actual .halt pFinal.stk rewindMemory
    (pFinal.stk 0) (pFinal.stk 1) (pFinal.stk 2)
  have rPath:=rewind_path .halt rRun rBefore rFinal rFirst rChain rLast rfl
  have shared : rewindCfg rBefore=pFinal := by
    have active:=pFacts.active
    rcases pFinal with ⟨position,memory,contents⟩
    change position=some (.rewind default) at active
    subst position
    change (⟨some (.rewind default),Restore.copyIso (C × RawNative.NativeMemory)
      ((Restore.copyIso (C × RawNative.NativeMemory)).symm memory),_⟩ : State C)=
      ⟨some (.rewind default),memory,contents⟩
    rw [Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot <;> rfl
  have finalBank : (rewindCfg rFinal).stk=outputBank bits I.stageCount I.toolCount budget := by
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
      exact pFacts.cacheN
    by_cases n9 : slot=9
    · subst slot
      exact pFacts.cacheJ
    by_cases n15 : slot=15
    · subst slot
      exact pFacts.budgetPacket
    simp only [Rewind.bank,outputBank,n0,n1,n2,n8,n9,n15,ite_false]
    exact pFacts.free slot n0 n1 n2 n8 n9 n15
  let before:=entry context bits
  have initialBound : ∀ slot,(before.stk slot).length≤bits.length := by
    intro slot
    have bound:=RatInput.Encoder.point_mass before.stk slot
    rw [entry_mass] at bound
    exact bound
  have initialFrame : ∀ slot,¬Work slot→before.stk slot=[] := by
    intro slot untouched
    have n0 : slot≠0 := by intro equal; subst slot; exact untouched (by decide)
    rw [entry_slots]
    simp only [n0,ite_false]
  have bounds:=trace_resources pRun before (fun _ => []) bits.length pFacts.first pFacts.chain initialBound initialFrame
  have cap0 : (pFinal.stk 0).length≤bits.length+16*prefixTime bits.length :=
    ((bounds pFinal (List.mem_of_getLast? pFacts.last)).1 0).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 16 pFacts.time) _)
  have cap1 : (pFinal.stk 1).length≤bits.length+16*prefixTime bits.length :=
    ((bounds pFinal (List.mem_of_getLast? pFacts.last)).1 1).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 16 pFacts.time) _)
  let front : Segment .halt (entry context bits) pFinal (prefixTime bits.length):=
    ⟨pRun,pFacts.first,pFacts.chain,pFacts.last,pFacts.time⟩
  let back : Segment .halt pFinal (rewindCfg rFinal)
      ((pFinal.stk 0).length+(pFinal.stk 1).length+(pFinal.stk 2).length+4):=
    ⟨rRun.map rewindCfg,rPath.1.trans (congrArg some shared),rPath.2.1,rPath.2.2,
      by simpa only [List.length_map] using Nat.le_of_eq rTime⟩
  let whole:=front.append back
  have rewindCap : (pFinal.stk 0).length+(pFinal.stk 1).length+(pFinal.stk 2).length+4≤
      32*prefixTime bits.length+3*bits.length+4 := by
    rw [backup,List.length_reverse]
    nlinarith only [cap0,cap1]
  have count : whole.trace.length≤33*prefixTime bits.length+3*bits.length+4 := by
    have old:=whole.count
    omega
  have base : 1≤bits.length+1 := by omega
  have linear : bits.length+1≤(bits.length+1)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right base (by decide : (1:Nat)≤3)
  have quad : (bits.length+1)^2≤(bits.length+1)^3 := Nat.pow_le_pow_right base (by decide : (2:Nat)≤3)
  refine ⟨whole.trace,rewindCfg rFinal,whole.head,whole.chain,whole.last,rfl,finalBank,?_⟩
  dsimp only [prefixTime,rawTime] at count
  change whole.trace.length≤4294967296*(bits.length+1)^3
  nlinarith only [count,linear,quad,base]

end RootB234.PrepEntry.Budget
