module

public import RootB234_PrepEntry_RawEOF_020
public import RootB234_PrepEntry_BudgetPrefix_022

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.RawNative

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRTMWordPreparationFront214 PSTRSymbolicRawLoop PSTRSymbolicCursorArchive
open PSTRTMIncrement009

abbrev Label := Fin 2
abbrev NativeMemory := VirtualBool.OldStore (states := loopSupport.card)
abbrev Store (C : Type*) := C × NativeMemory
abbrev Statement (C : Type*) := VirtualReturn.Statement C NativeMemory
abbrev State (C : Type*) := VirtualReturn.State C NativeMemory

variable {C : Type*} {I : Instance}

noncomputable def source : Unit → VirtualReturn.SmallStatement NativeMemory := VirtualBool.source rawLoopMachine

noncomputable def program (caller : Statement C) : Label → Statement C := VirtualReturn.program source caller

def entry (context : C) (background : RatInput.Stack → List Bool) (bits : List Bool) : State C :=
  VirtualReturn.configuration context background
    (TM2.init (Γ := PushPop.Alphabet) (Λ := Unit) (σ := NativeMemory) 0 bits)

theorem program_actions (point : Label) : ScannerClock.actions (program (C := C) .halt point)≤4 := by
  fin_cases point
  · exact Nat.le_of_eq (VirtualBool.actions rawLoopMachine)
  · exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C := C) .halt point)≤2 := by
  fin_cases point
  · exact Nat.le_of_eq (VirtualBool.pushes rawLoopMachine)
  · exact of_decide_eq_true rfl

theorem point_mass (bank : RatInput.Stack → List Bool) (slot : RatInput.Stack) :
    (bank slot).length≤VirtualReturn.occupiedSlots bank := by
  fin_cases slot <;> dsimp [VirtualReturn.occupiedSlots] <;> omega

theorem work_mass (bank : RatInput.Stack → List Bool) :
    (bank 0).length+(bank 1).length≤VirtualReturn.occupiedSlots bank := by
  dsimp [VirtualReturn.occupiedSlots]
  omega

theorem outside_mass (bank : RatInput.Stack → List Bool) :
    VirtualReturn.outside bank≤VirtualReturn.occupiedSlots bank := by
  dsimp [VirtualReturn.outside,VirtualReturn.occupiedSlots]
  omega

theorem body_internal (memory : Store C) (bank : RatInput.Stack → List Bool) :
    ∀ node∈AuxWorkspace.nodes (program .halt 0) memory bank,
      node.1.1=memory.1 ∧
      (∀ slot,slot≠0→slot≠1→node.2 slot=bank slot) ∧
      VirtualReturn.occupiedSlots node.2≤VirtualReturn.outside bank+
        2*((bank 0).length+(bank 1).length+2) := by
  rcases memory with ⟨context,localMemory⟩
  let small : PushPop.Stack → List Bool:=fun slot => bank (VirtualReturn.role slot)
  have rebuild : VirtualReturn.slots bank small=bank := by
    funext slot
    fin_cases slot <;> rfl
  have old:=VirtualBool.internal_resources rawLoopMachine context localMemory small bank
  rw [rebuild] at old
  exact old

theorem initial_default (bits : List Bool) :
    entry () (fun _ => []) bits=TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store Unit) 0 bits := by
  change (⟨some 0,((),default),_⟩ : State Unit)=⟨some 0,((),default),_⟩
  congr 1
  funext slot
  fin_cases slot <;> rfl

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C := C) .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

abbrev finiteStore (C : Type*) [Fintype C] : Fintype (Store C) := inferInstance

structure Facts (caller : Statement C) (context : C) (background : RatInput.Stack → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat)
    (digits : List Bool) (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (entry context background (preparationInput input contract budget))
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final
  active : final.l=some 1
  tape : Tape.mk' (ListBlank.mk (final.stk 1)) (ListBlank.mk (final.stk 0))=
    archiveTape (preparationData input contract budget) [] digits [] true
  zero : valueDigits digits=0
  width : 3≤digits.length
  budget_prefix : ∃ (boundary : Bool) (tail : List Bool),final.stk 1=Raw.budgetPairBits budget++boundary::true::tail
  time : trace.length≤4097*((preparationInput input contract budget).length+1)^3
  frames : ∀ current∈trace,current.var.1=context ∧
    ∀ slot,slot≠0→slot≠1→current.stk slot=background slot
  mass : ∀ current∈trace,VirtualReturn.occupiedSlots current.stk≤VirtualReturn.outside background+
    16384*((preparationInput input contract budget).length+1)^3

/-- ONE old frozen full-Datum source on the true preparation wire. The
outer M is actually read and consumed by that source; no width/count/fuel
is caller supplied, and N=0 is covered by original contract room. -/
theorem actual (caller : Statement C) (context : C) (background : RatInput.Stack → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ digits trace final,Facts caller context background input contract budget digits trace final := by
  obtain ⟨digits,oldTrace,oldFinal,old,oldTape,value,width,time,space⟩:=Raw.preparation_raw_polynomial input contract budget
  obtain ⟨trace,final,first,chain,last,active,represented,_order,count,_context,frames,mass⟩:=
    VirtualBool.same_old_run rawLoopMachine caller context background (preparationInput input contract budget)
      oldTrace oldFinal old.1 old.2.1 old.2.2.1 old.2.2.2.1
  have tape:=congrArg TM0.Cfg.Tape represented
  rw [oldTape] at tape
  have wholeLeft:=congrArg Tape.left tape
  change ListBlank.mk (final.stk 1)=(archiveTape (preparationData input contract budget) [] digits [] true).left at wholeLeft
  have physical:=Raw.finite_budget_prefix input contract budget digits (final.stk 1) wholeLeft
  have cells:=space oldTrace.length
  simp only [List.take_length] at cells
  have positive : 1≤((preparationInput input contract budget).length+1)^3:=
    Nat.pow_le_pow_left (show 1≤(preparationInput input contract budget).length+1 by omega) 3
  refine ⟨digits,trace,final,⟨first,chain,last,active,tape,value,width,physical,?_,frames,?_⟩⟩
  · rw [count]
    omega
  · intro current present
    exact (mass current present).trans (Nat.add_le_add_left cells _)

variable {context : C} {background : RatInput.Stack → List Bool} {input : StatisticalInput I}
  {contract : Contract I} {budget : Rat} {digits : List Bool} {trace : List (State C)} {final : State C}

/-- Every executed primitive keeps C and all non0/1 stacks. The active
return1 caller is excluded, and its code/cost is not charged. -/
theorem proper_resources (facts : Facts .halt context background input contract budget digits trace final) :
    ∀ current∈trace.dropLast,current.l≠some 1 ∧
      ∀ point,current.l=some point→
        (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
          node.1.1=context ∧
          (∀ slot,(node.2 slot).length≤3*VirtualReturn.outside background+
            65536*((preparationInput input contract budget).length+1)^3) ∧
          VirtualReturn.occupiedSlots node.2≤3*VirtualReturn.outside background+
            65536*((preparationInput input contract budget).length+1)^3 ∧
          ∀ slot,slot≠0→slot≠1→node.2 slot=background slot) ∧
        ScannerStatement.clock (program .halt point) current.var current.stk≤
          8*VirtualReturn.outside background+262144*((preparationInput input contract budget).length+1)^3 := by
  have proper:=NativeMulLink.no_early_halt_port (program .halt) 1 rfl trace final facts.chain facts.last facts.active
  intro current present
  refine ⟨proper current present,?_⟩
  intro point selected
  have frame:=facts.frames current (List.mem_of_mem_dropLast present)
  have mass:=facts.mass current (List.mem_of_mem_dropLast present)
  have work:=work_mass current.stk
  have outside:=outside_mass current.stk
  have base : 1≤((preparationInput input contract budget).length+1)^3:=Nat.pow_le_pow_left (show 1≤(preparationInput input contract budget).length+1 by omega) 3
  have zero : point=0 := by
    fin_cases point
    · rfl
    · exact False.elim (proper current present selected)
  subst point
  have inside:=body_internal current.var current.stk
  have bounded : ∀ slot,(current.stk slot).length≤VirtualReturn.outside background+
      16384*((preparationInput input contract budget).length+1)^3 := fun slot => (point_mass _ slot).trans mass
  refine ⟨?_,?_⟩
  · intro node member
    have nodeFacts:=inside node member
    have cap : VirtualReturn.occupiedSlots node.2≤3*VirtualReturn.outside background+
        65536*((preparationInput input contract budget).length+1)^3 := by
      nlinarith only [nodeFacts.2.2,work,outside,mass,base]
    exact ⟨nodeFacts.1.trans frame.1,fun slot => (point_mass _ slot).trans cap,cap,
      fun slot n0 n1 => (nodeFacts.2.1 slot n0 n1).trans (frame.2 slot n0 n1)⟩
  · have clock:=(ScannerClock.clock_bound (program .halt 0) current.var current.stk _ bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions (C := C) 0))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes (C := C) 0) _) 1))
    nlinarith only [clock,base]

noncomputable def statementClock (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program .halt point) current.var current.stk

noncomputable def traceClockSum (trace : List (State C)) : Nat := (trace.dropLast.map statementClock).sum

noncomputable def chargedCost (trace : List (State C)) : Nat := trace.length+traceClockSum trace

theorem traceClockSum_le (facts : Facts .halt context background input contract budget digits trace final) :
    traceClockSum trace≤4097*((preparationInput input contract budget).length+1)^3*
      (8*VirtualReturn.outside background+262144*((preparationInput input contract budget).length+1)^3) := by
  let cap:=8*VirtualReturn.outside background+262144*((preparationInput input contract budget).length+1)^3
  have termwise : ∀ value∈trace.dropLast.map statementClock,value≤cap := by
    intro value member
    obtain ⟨current,present,rfl⟩:=List.mem_map.mp member
    cases selected : current.l with
    | none => simp only [statementClock,selected,Nat.zero_le]
    | some point =>
      simp only [statementClock,selected]
      exact ((proper_resources facts current present).2 point selected).2
  have sum : traceClockSum trace≤trace.dropLast.length*cap := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (trace.dropLast.map statementClock) cap termwise
  have length : trace.dropLast.length≤4097*((preparationInput input contract budget).length+1)^3 := by
    rw [List.length_dropLast]
    exact (Nat.sub_le trace.length 1).trans facts.time
  exact sum.trans (Nat.mul_le_mul_right cap length)

theorem original_charge_le (facts : Facts .halt context (fun _ => []) input contract budget digits trace final) :
    chargedCost trace≤2147483648*(arithmeticScale input contract budget)^6 := by
  have sum:=traceClockSum_le facts
  have count:=facts.time
  have positive : 1≤(preparationInput input contract budget).length+1 := by omega
  have powers : ((preparationInput input contract budget).length+1)^3≤((preparationInput input contract budget).length+1)^6 :=
    Nat.pow_le_pow_right positive (by decide : (3:Nat)≤6)
  have inputPower:=Nat.pow_le_pow_left (Nat.length_le_arithmeticScale input contract budget) 6
  simp only [VirtualReturn.outside,List.length_nil] at sum
  dsimp only [chargedCost]
  have charge : trace.length+traceClockSum trace≤2147483648*((preparationInput input contract budget).length+1)^6 := by
    nlinarith only [sum,count,powers]
  exact charge.trans (Nat.mul_le_mul_left _ inputPower)


namespace Public

theorem fixed_source (C : Type*) [Fintype C] :
    ∃ (code : Label → Statement C) (labels : Finset Label),
      TM2.Supports code labels ∧ code 1=.halt ∧
      ∀ {I : Instance} (context : C) (background : RatInput.Stack → List Bool)
        (input : StatisticalInput I) (contract : Contract I) (budget : Rat),
        ∃ digits trace final,Facts .halt context background input contract budget digits trace final ∧
          trace.IsChain (fun a b => TM2.step code a=some b) := by
  refine ⟨program .halt,Finset.univ,supports,rfl,?_⟩
  intro I context background input contract budget
  obtain ⟨digits,trace,final,facts⟩:=actual .halt context background input contract budget
  exact ⟨digits,trace,final,facts,facts.chain⟩

theorem from_default (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ digits trace final,Facts .halt () (fun _ => []) input contract budget digits trace final ∧
      trace.head?=some (TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store Unit) 0
        (preparationInput input contract budget)) := by
  obtain ⟨digits,trace,final,facts⟩:=actual .halt () (fun _ => []) input contract budget
  exact ⟨digits,trace,final,facts,facts.first.trans (congrArg some (initial_default _))⟩

end Public
end RootB234.PrepEntry.RawNative
