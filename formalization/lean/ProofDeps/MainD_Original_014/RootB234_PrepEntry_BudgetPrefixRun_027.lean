module

public import RootB234_PrepEntry_BudgetSyntax_026

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

def rawTime (length : Nat) : Nat := 262144*(length+1)^2+(2*length+4)+4097*(length+1)^3

def prefixTime (length : Nat) : Nat := rawTime length+16*(length+16*rawTime length)+7

structure PrefixFacts (context : C) (input : StatisticalInput I) (contract : Contract I) (budget : Rat)
    (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (entry context (preparationInput input contract budget))
  chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b)
  last : trace.getLast?=some final
  active : final.l=some (.rewind default)
  cacheN : final.stk 8=NatField.packet I.stageCount []
  cacheJ : final.stk 9=NatField.packet I.toolCount []
  budgetPacket : final.stk 15=RatInput.Encoder.packet budget []
  backup : final.stk 2=(preparationInput input contract budget).reverse
  free : ∀ slot,slot≠0→slot≠1→slot≠2→slot≠8→slot≠9→slot≠15→final.stk slot=[]
  time : trace.length≤prefixTime (preparationInput input contract budget).length

/-- The whole original-input prefix reaches the real final rewind entry.
The budget source consumes the actual paired archive; its three flags are
the original preallocated NaturalExport flags with no reset. -/
theorem actual_prefix (context : C) (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ trace final,PrefixFacts context input contract budget trace final := by
  let bits:=preparationInput input contract budget
  obtain ⟨rRun,rFinal,rFirst,rChain,rLast,rActive,rBank,rTime⟩:=
    Restore.actual .halt (context,(default : RawNative.NativeMemory)) input contract budget
  have rPath:=restore_path .halt rRun _ rFinal rFirst rChain rLast rActive
  have rContext:=Restore.trace_context rRun (Restore.entry (context,(default : RawNative.NativeMemory)) bits)
    rFirst rChain rFinal (List.mem_of_getLast? rLast)
  change rFinal.var.1.1.1.1=(context,(default : RawNative.NativeMemory)) at rContext
  let copyMemory:=(Restore.copyIso (C × RawNative.NativeMemory)).symm rFinal.var
  let cBefore:=WholeCopy.state rFinal.stk .boot copyMemory bits [] []
  let cFinal:=WholeCopy.state rFinal.stk .done (copyMemory.1,true,true) bits (bits.reverse++[]) []
  obtain ⟨cRun,cFirst,cChain,cLast,cTime⟩:=WholeCopy.actual .halt rFinal.stk copyMemory bits [] []
  have cPath:=copy_path .halt cRun cBefore cFinal cFirst cChain cLast rfl
  have rCopy : copyCfg cBefore=restoreCfg rFinal := by
    rcases rFinal with ⟨position,memory,contents⟩
    change position=some Restore.Label.done at rActive
    subst position
    change (⟨some (.copy .boot),Restore.copyIso (C × RawNative.NativeMemory)
      ((Restore.copyIso (C × RawNative.NativeMemory)).symm memory),_⟩ : State C)=
      ⟨some (.copy .boot),memory,contents⟩
    rw [Equiv.apply_symm_apply]
    congr 1
    change WholeCopy.bank contents bits [] []=contents
    change contents=Restore.outputBank bits I.stageCount I.toolCount at rBank
    rw [rBank]
    funext slot
    fin_cases slot <;> rfl
  let rawMemory:=(rawIso C).symm (copyCfg cFinal).var
  let rawContext:=rawMemory.1
  have rawDefault : rawMemory.2=default := by
    change rFinal.var.1.1.1.1.2=default
    exact congrArg Prod.snd rContext
  have copied0 : cFinal.stk 0=bits := rfl
  have copied1 : cFinal.stk 1=[] := by
    change rFinal.stk 1=[]
    rw [rBank]
    rfl
  have rawBank : (RawNative.entry rawContext cFinal.stk bits).stk=cFinal.stk := by
    funext slot
    by_cases n0 : slot=0
    · subst slot
      exact copied0.symm
    by_cases n1 : slot=1
    · subst slot
      exact copied1.symm
    exact VirtualReturn.slots_frame _ _ slot n0 n1
  have cRaw : rawCfg (RawNative.entry rawContext cFinal.stk bits)=copyCfg cFinal := by
    have memoryEq : rawIso C (rawContext,default)=(copyCfg cFinal).var := by
      rw [←rawDefault]
      change rawIso C ((rawIso C).symm (copyCfg cFinal).var)=_
      exact Equiv.apply_symm_apply _ _
    change (⟨some (.raw 0),rawIso C (rawContext,default),_⟩ : State C)=
      ⟨some (.raw 0),(copyCfg cFinal).var,cFinal.stk⟩
    rw [memoryEq]
    congr 1
  obtain ⟨digits,aRun,aFinal,aFacts⟩:=RawNative.actual .halt rawContext cFinal.stk input contract budget
  have aPath:=raw_path .halt aRun _ aFinal aFacts.first aFacts.chain aFacts.last aFacts.active
  let front : Segment .halt (entry context bits) (restoreCfg rFinal) (262144*(bits.length+1)^2):=
    ⟨rRun.map restoreCfg,rPath.1,rPath.2.1,rPath.2.2,by simpa only [List.length_map] using rTime⟩
  let copied : Segment .halt (restoreCfg rFinal) (copyCfg cFinal) (2*bits.length+4):=
    ⟨cRun.map copyCfg,cPath.1.trans (congrArg some rCopy),cPath.2.1,cPath.2.2,
      by simpa only [List.length_map] using Nat.le_of_eq cTime⟩
  let parsed : Segment .halt (copyCfg cFinal) (rawCfg aFinal) (4097*(bits.length+1)^3):=
    ⟨aRun.map rawCfg,aPath.1.trans (congrArg some cRaw),aPath.2.1,aPath.2.2,
      by simpa only [List.length_map] using aFacts.time⟩
  let throughRaw:=(front.append copied).append parsed
  have rawCount : throughRaw.trace.length≤rawTime bits.length:=throughRaw.count
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
  have bounds:=trace_resources throughRaw.trace before (fun _ => []) bits.length throughRaw.head throughRaw.chain initialBound initialFrame
  have rawEach : ∀ slot,(aFinal.stk slot).length≤bits.length+16*rawTime bits.length := by
    intro slot
    exact ((bounds (rawCfg aFinal) (List.mem_of_getLast? throughRaw.last)).1 slot).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 16 rawCount) _)
  have rawMass:=RatInput.Encoder.occupied_bound aFinal.stk _ rawEach
  let bMemory:=(budgetIso C).symm (rawCfg aFinal).var
  obtain ⟨bRun,bFinal,bFirst,bChain,bLast,bActive,_bContext,bPacket,bFrame,bTime⟩:=
    BudgetField.actual_current .halt bMemory aFinal.stk budget aFacts.budget_prefix
  have bPath:=budget_path .halt bRun _ bFinal bFirst bChain bLast bActive
  have aBudget : budgetCfg (⟨some 0,bMemory,aFinal.stk⟩ : RootB234.PrepBudgetArchive.State (BudgetContext C))=
      rawCfg aFinal := by
    have aActive:=aFacts.active
    rcases aFinal with ⟨position,memory,contents⟩
    change position=some 1 at aActive
    subst position
    change (⟨some (.budget 0),budgetIso C ((budgetIso C).symm (rawIso C memory)),contents⟩ : State C)=
      ⟨some (.budget 0),rawIso C memory,contents⟩
    rw [Equiv.apply_symm_apply]
  let exported : Segment .halt (rawCfg aFinal) (budgetCfg bFinal) (RatInput.occupied aFinal.stk+7):=
    ⟨bRun.map budgetCfg,bPath.1.trans (congrArg some aBudget),bPath.2.1,bPath.2.2,
      by simpa only [List.length_map] using bTime⟩
  let whole:=throughRaw.append exported
  have aFrame:=(aFacts.frames aFinal (List.mem_of_getLast? aFacts.last)).2
  have cacheN : aFinal.stk 8=NatField.packet I.stageCount [] := by
    rw [aFrame 8 (by decide) (by decide)]
    change rFinal.stk 8=_
    rw [rBank]
    rfl
  have cacheJ : aFinal.stk 9=NatField.packet I.toolCount [] := by
    rw [aFrame 9 (by decide) (by decide)]
    change rFinal.stk 9=_
    rw [rBank]
    rfl
  have backup : aFinal.stk 2=bits.reverse := by
    rw [aFrame 2 (by decide) (by decide)]
    change bits.reverse++[]=bits.reverse
    exact List.append_nil _
  have targetEmpty : aFinal.stk 15=[] := by
    rw [aFrame 15 (by decide) (by decide)]
    change rFinal.stk 15=[]
    rw [rBank]
    rfl
  refine ⟨whole.trace,budgetCfg bFinal,⟨whole.head,whole.chain,whole.last,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · change bFinal.l.map budgetLabel=some (.rewind default)
    rw [bActive]
    rfl
  · exact (bFrame 8 (by decide) (by decide)).trans cacheN
  · exact (bFrame 9 (by decide) (by decide)).trans cacheJ
  · exact bPacket.trans (congrArg (RatInput.Encoder.packet budget) targetEmpty)
  · exact (bFrame 2 (by decide) (by decide)).trans backup
  · intro slot n0 n1 n2 n8 n9 n15
    change bFinal.stk slot=[]
    rw [bFrame slot n1 n15,aFrame slot n0 n1]
    change WholeCopy.bank rFinal.stk bits (bits.reverse++[]) [] slot=[]
    by_cases n3 : slot=3
    · subst slot
      rfl
    simp only [WholeCopy.bank,n0,n2,n3,ite_false,rBank,Restore.outputBank,n8,n9]
  · have count:=whole.count
    change whole.trace.length≤rawTime bits.length+(RatInput.occupied aFinal.stk+7) at count
    change whole.trace.length≤prefixTime bits.length
    dsimp only [prefixTime]
    omega

end RootB234.PrepEntry.Budget
