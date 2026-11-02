module
public import RootB234_RuntimeCounter_Builder_Resources003

/-! Static roles are selected before the input. Renaming transports the
same physical path, every internal node, and the actual scanner clock. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.RuntimeCounter.Builder
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
variable {C : Type*}

theorem clock_statement (roles : Stack ≃ Stack) (body : Statement C)
    (memory : Store C) (before : Stack → List Bool) :
    ScannerStatement.clock (StackIso.statement roles body) memory (StackIso.slots roles before)=
      ScannerStatement.clock body memory before := RatPacketTransport.clock_statement roles body memory before

def atProgram (roles : Stack ≃ Stack) (doubled : Bool) (point : Label) : Statement C :=
  StackIso.statement roles (program doubled .halt point)

def atBank (roles : Stack ≃ Stack) (background : Stack → List Bool) (source temporary counter leftguard : List Bool) :
    Stack → List Bool :=
  fun slot => if slot=roles 8 then source else if slot=roles 4 then temporary
    else if slot=roles 10 then counter else if slot=roles 11 then leftguard else background slot

def atState (roles : Stack ≃ Stack) (background : Stack → List Bool) (point : Label)
    (context : C) (memory : RatOutput.Store) (source temporary counter leftguard : List Bool) : State C :=
  ⟨some point,(context,memory),atBank roles background source temporary counter leftguard⟩

def AtWork (roles : Stack ≃ Stack) (slot : Stack) : Prop :=
  slot=roles 4 ∨ slot=roles 8 ∨ slot=roles 10 ∨ slot=roles 11

theorem atWork_iff (roles : Stack ≃ Stack) (slot : Stack) :
    AtWork roles slot ↔ Work (roles.symm slot) := by
  simp only [AtWork,Work,Equiv.symm_apply_eq]

theorem slots_inverse (roles : Stack ≃ Stack) (background : Stack → List Bool) :
    StackIso.slots roles (StackIso.slots roles.symm background)=background := by
  funext slot
  simp only [StackIso.slots,Equiv.symm_symm,Equiv.apply_symm_apply]

theorem atBank_eq (roles : Stack ≃ Stack) (background : Stack → List Bool) (source temporary counter leftguard : List Bool) :
    atBank roles background source temporary counter leftguard=
      StackIso.slots roles (bank (StackIso.slots roles.symm background) source temporary counter leftguard) := by
  funext slot
  simp only [atBank,StackIso.slots,bank,Equiv.symm_apply_eq,Equiv.symm_symm,Equiv.apply_symm_apply]

theorem atState_eq (roles : Stack ≃ Stack) (background : Stack → List Bool) (point : Label)
    (context : C) (memory : RatOutput.Store) (source temporary counter leftguard : List Bool) :
    atState roles background point context memory source temporary counter leftguard=
      StackIso.configuration roles
        (state (StackIso.slots roles.symm background) point context memory source temporary counter leftguard) := by
  rw [atState,atBank_eq];rfl

theorem occupied_slots (roles : Stack ≃ Stack) (before : Stack → List Bool) :
    RatInput.occupied (StackIso.slots roles before)=RatInput.occupied before :=
  StackIso.occupied_sum roles before

def atScale (roles : Stack ≃ Stack) (background : Stack → List Bool) (number : Nat) (source old10 old11 : List Bool) : Nat :=
  RatInput.occupied (atBank roles background (B23_4_RatWordPrep.NatField.packet number source) [] old10 old11)+1

theorem atScale_eq (roles : Stack ≃ Stack) (background : Stack → List Bool) (number : Nat) (source old10 old11 : List Bool) :
    atScale roles background number source old10 old11=inputScale (StackIso.slots roles.symm background) number source old10 old11 := by
  rw [atScale,atBank_eq,occupied_slots];rfl

def atStatementClock (roles : Stack ≃ Stack) (doubled : Bool) (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (atProgram roles doubled point) current.var current.stk

def atClockSum (roles : Stack ≃ Stack) (doubled : Bool) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (atStatementClock roles doubled)).sum

def atCharge (roles : Stack ≃ Stack) (doubled : Bool) (trace : List (State C)) : Nat :=
  trace.length+atClockSum roles doubled trace

structure AtFacts (roles : Stack ≃ Stack) (doubled : Bool) (background : Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (number : Nat) (source old10 old11 : List Bool) (trace : List (State C)) : Prop where
  first : trace.head?=some (atState roles background 0 context memory (B23_4_RatWordPrep.NatField.packet number source) [] old10 old11)
  chain : trace.IsChain (fun a b => TM2.step (atProgram roles doubled) a=some b)
  last : trace.getLast?=some (atState roles background 5 context (false,false) (B23_4_RatWordPrep.NatField.packet number source) []
    (PSTRTMIncrement009.blocks (selectDigits doubled (PSTRTMNatValue017.rawPayload number))++[false,false,true]) [false])
  count : trace.length≤old10.length+old11.length+2*(PSTRTMNatValue017.rawPayload number).length+14
  time : trace.length≤coefficient*atScale roles background number source old10 old11
  boundaries : ∀ current∈trace,current.var.1=context ∧
    (∀ slot,(current.stk slot).length≤coefficient*atScale roles background number source old10 old11) ∧
    RatInput.occupied current.stk≤coefficient*atScale roles background number source old10 old11 ∧
    ∀ slot,¬AtWork roles slot→current.stk slot=background slot
  proper : ∀ current∈trace.dropLast,current.l≠some 5 ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (atProgram roles doubled point) current.var current.stk,
        node.1.1=context ∧
        (∀ slot,(node.2 slot).length≤coefficient*atScale roles background number source old10 old11) ∧
        RatInput.occupied node.2≤coefficient*atScale roles background number source old10 old11 ∧
        ∀ slot,¬AtWork roles slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (atProgram roles doubled point) current.var current.stk≤coefficient*atScale roles background number source old10 old11
  clockSum : atClockSum roles doubled trace≤coefficient^2*(atScale roles background number source old10 old11)^2
  charge : atCharge roles doubled trace≤(coefficient^2+coefficient)*(atScale roles background number source old10 old11)^2

theorem at_actual (roles : Stack ≃ Stack) (doubled : Bool) (background : Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (number : Nat) (source old10 old11 : List Bool) :
    ∃ trace,AtFacts roles doubled background context memory number source old10 old11 trace := by
  let bg:=StackIso.slots roles.symm background
  obtain ⟨trace,facts⟩:=actual_bounded doubled bg context memory number source old10 old11
  have scale : atScale roles background number source old10 old11=inputScale bg number source old10 old11:=atScale_eq _ _ _ _ _ _
  have clock (current : State C) :
      atStatementClock roles doubled (StackIso.configuration roles current)=statementClock doubled current := by
    cases selected : current.l <;> simp only [atStatementClock,statementClock,StackIso.configuration,selected]
    exact clock_statement roles _ _ _
  have clockSum : atClockSum roles doubled (trace.map (StackIso.configuration roles))=traceClockSum doubled trace := by
    simp only [atClockSum,traceClockSum,←List.map_dropLast,List.map_map,Function.comp_def,clock]
  have charge : atCharge roles doubled (trace.map (StackIso.configuration roles))=chargedCost doubled trace := by
    rw [atCharge,clockSum,List.length_map];rfl
  refine ⟨trace.map (StackIso.configuration roles),⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · rw [List.head?_map,facts.first,Option.map_some,atState_eq]
  · exact StackIso.chain_configuration_on roles _ _ trace facts.chain (by intros;rfl)
  · rw [List.getLast?_map,facts.last,Option.map_some,atState_eq]
  · simpa only [List.length_map] using facts.count
  · simpa only [List.length_map,scale] using facts.time
  · intro current member
    obtain ⟨old,present,rfl⟩:=List.mem_map.mp member
    have bound:=facts.boundaries old present
    refine ⟨bound.1,fun slot => ?_,?_,?_⟩
    · simpa only [StackIso.configuration,StackIso.slots,scale] using bound.2.1 (roles.symm slot)
    · simpa only [StackIso.configuration,occupied_slots,scale] using bound.2.2.1
    · intro slot untouched
      have frame:=bound.2.2.2 (roles.symm slot) ((atWork_iff roles slot).not.mp untouched)
      simpa only [StackIso.configuration,StackIso.slots,bg,Equiv.symm_symm,Equiv.apply_symm_apply] using frame
  · intro current member
    rw [←List.map_dropLast] at member
    obtain ⟨old,present,rfl⟩:=List.mem_map.mp member
    have bound:=facts.proper old present
    refine ⟨bound.1,?_⟩
    intro point selected
    have internal:=bound.2 point selected
    refine ⟨?_,?_⟩
    · intro node inside
      rw [atProgram,StackIso.configuration,StackIso.nodes_statement] at inside
      obtain ⟨oldNode,oldInside,rfl⟩:=List.mem_map.mp inside
      have nodeBound:=internal.1 oldNode oldInside
      refine ⟨nodeBound.1,fun slot => ?_,?_,?_⟩
      · simpa only [StackIso.slots,scale] using nodeBound.2.1 (roles.symm slot)
      · simpa only [occupied_slots,scale] using nodeBound.2.2.1
      · intro slot untouched
        have frame:=nodeBound.2.2.2 (roles.symm slot) ((atWork_iff roles slot).not.mp untouched)
        simpa only [StackIso.slots,bg,Equiv.symm_symm,Equiv.apply_symm_apply] using frame
    · simpa only [atProgram,StackIso.configuration,clock_statement,scale] using internal.2
  · rw [clockSum,scale];exact traceClockSum_le facts
  · rw [charge,scale];exact chargedCost_le facts

theorem at_supports (roles : Stack ≃ Stack) (doubled : Bool) :
    TM2.Supports (atProgram (C:=C) roles doubled) support := by
  refine ⟨Finset.mem_univ _,?_⟩
  intro point member
  exact (StackIso.statement_supports roles _ support).mpr ((supports doubled).2 point member)

end RootB234.RuntimeCounter.Builder
