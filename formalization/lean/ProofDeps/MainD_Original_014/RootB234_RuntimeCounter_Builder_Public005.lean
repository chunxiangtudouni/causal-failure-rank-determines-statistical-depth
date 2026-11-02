module
public import RootB234_RuntimeCounter_Builder_Rename004

/-! Literal source8/source1, N/2N instances. The original packet and its
arbitrary tail are restored; counter10/leftguard11 have a real markerTRUE.
There is no width, fuel, count answer or default-context caller premise. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.RuntimeCounter.Builder.Public
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
variable {C : Type*}

theorem finite_store [Finite C] : Finite (Store C) := inferInstance

def source8Roles : Stack ≃ Stack := Equiv.refl _
def source1Roles : Stack ≃ Stack := Equiv.swap 8 1
def from8N : Label → Statement C := atProgram source8Roles false
def from8Twice : Label → Statement C := atProgram source8Roles true
def from1N : Label → Statement C := atProgram source1Roles false
def from1Twice : Label → Statement C := atProgram source1Roles true

def physicalBank (source : Stack) (background : Stack → List Bool)
    (input temporary counter leftguard : List Bool) : Stack → List Bool :=
  fun slot => if slot=source then input else if slot=4 then temporary
    else if slot=10 then counter else if slot=11 then leftguard else background slot

def physicalState (source : Stack) (background : Stack → List Bool) (point : Label)
    (context : C) (memory : RatOutput.Store) (input temporary counter leftguard : List Bool) : State C :=
  ⟨some point,(context,memory),physicalBank source background input temporary counter leftguard⟩

theorem source8_state (background : Stack → List Bool) (point : Label) (context : C)
    (memory : RatOutput.Store) (input temporary counter leftguard : List Bool) :
    atState source8Roles background point context memory input temporary counter leftguard=
      physicalState 8 background point context memory input temporary counter leftguard := rfl

theorem source1_state (background : Stack → List Bool) (point : Label) (context : C)
    (memory : RatOutput.Store) (input temporary counter leftguard : List Bool) :
    atState source1Roles background point context memory input temporary counter leftguard=
      physicalState 1 background point context memory input temporary counter leftguard := rfl

theorem from8N_actual (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (old8 old10 old11 : List Bool) :
    ∃ trace,AtFacts source8Roles false background context memory number old8 old10 old11 trace :=
  at_actual _ _ _ _ _ _ _ _ _
theorem from8Twice_actual (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (old8 old10 old11 : List Bool) :
    ∃ trace,AtFacts source8Roles true background context memory number old8 old10 old11 trace :=
  at_actual _ _ _ _ _ _ _ _ _
theorem from1N_actual (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (old1 old10 old11 : List Bool) :
    ∃ trace,AtFacts source1Roles false background context memory number old1 old10 old11 trace :=
  at_actual _ _ _ _ _ _ _ _ _
theorem from1Twice_actual (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (old1 old10 old11 : List Bool) :
    ∃ trace,AtFacts source1Roles true background context memory number old1 old10 old11 trace :=
  at_actual _ _ _ _ _ _ _ _ _

theorem from8N_supports : TM2.Supports (from8N (C:=C)) support := at_supports _ _
theorem from8Twice_supports : TM2.Supports (from8Twice (C:=C)) support := at_supports _ _
theorem from1N_supports : TM2.Supports (from1N (C:=C)) support := at_supports _ _
theorem from1Twice_supports : TM2.Supports (from1Twice (C:=C)) support := at_supports _ _

theorem source8_frame (slot : Stack) :
    ¬AtWork source8Roles slot ↔ slot≠4 ∧ slot≠8 ∧ slot≠10 ∧ slot≠11 := by
  simp only [AtWork,source8Roles,Equiv.refl_apply,not_or]
theorem source1_frame (slot : Stack) :
    ¬AtWork source1Roles slot ↔ slot≠4 ∧ slot≠1 ∧ slot≠10 ∧ slot≠11 := by
  change ¬(slot=4 ∨ slot=1 ∨ slot=10 ∨ slot=11) ↔ _
  simp only [not_or]

theorem digits_value (doubled : Bool) (number : Nat) :
    PSTRTMIncrement009.valueDigits (selectDigits doubled (PSTRTMNatValue017.rawPayload number))=
      if doubled then 2*number else number := by
  cases doubled <;> simp [selectDigits,PSTRTMIncrement009.valueDigits,PSTRTMNatValue017.valueDigits_rawPayload,Nat.bit]

theorem digits_length (doubled : Bool) (number : Nat) :
    (selectDigits doubled (PSTRTMNatValue017.rawPayload number)).length=
      (PSTRTMNatValue017.rawPayload number).length+(if doubled then 1 else 0) := by
  cases doubled <;> simp [selectDigits]

def finalState (roles : Stack ≃ Stack) (doubled : Bool) (background : Stack → List Bool)
    (context : C) (number : Nat) (source : List Bool) : State C :=
  atState roles background 5 context (false,false) (B23_4_RatWordPrep.NatField.packet number source) []
    (PSTRTMIncrement009.blocks (selectDigits doubled (PSTRTMNatValue017.rawPayload number))++[false,false,true]) [false]

def counterTape (current : State C) : Tape Bool := Tape.mk₂ (current.stk 11) (current.stk 10)

theorem source8_final_tape (doubled : Bool) (background : Stack → List Bool) (context : C)
    (number : Nat) (source : List Bool) : counterTape (finalState source8Roles doubled background context number source)=
      Tape.mk₂ [false] (PSTRTMIncrement009.blocks (selectDigits doubled (PSTRTMNatValue017.rawPayload number))++[false,false,true]) := rfl
theorem source1_final_tape (doubled : Bool) (background : Stack → List Bool) (context : C)
    (number : Nat) (source : List Bool) : counterTape (finalState source1Roles doubled background context number source)=
      Tape.mk₂ [false] (PSTRTMIncrement009.blocks (selectDigits doubled (PSTRTMNatValue017.rawPayload number))++[false,false,true]) := rfl

theorem source8_final_stacks (doubled : Bool) (background : Stack → List Bool) (context : C)
    (number : Nat) (source : List Bool) :
    (finalState source8Roles doubled background context number source).stk 8=B23_4_RatWordPrep.NatField.packet number source ∧
    (finalState source8Roles doubled background context number source).stk 4=[] ∧
    (finalState source8Roles doubled background context number source).stk 10=
      PSTRTMIncrement009.blocks (selectDigits doubled (PSTRTMNatValue017.rawPayload number))++[false,false,true] ∧
    (finalState source8Roles doubled background context number source).stk 11=[false] := ⟨rfl,rfl,rfl,rfl⟩
theorem source1_final_stacks (doubled : Bool) (background : Stack → List Bool) (context : C)
    (number : Nat) (source : List Bool) :
    (finalState source1Roles doubled background context number source).stk 1=B23_4_RatWordPrep.NatField.packet number source ∧
    (finalState source1Roles doubled background context number source).stk 4=[] ∧
    (finalState source1Roles doubled background context number source).stk 10=
      PSTRTMIncrement009.blocks (selectDigits doubled (PSTRTMNatValue017.rawPayload number))++[false,false,true] ∧
    (finalState source1Roles doubled background context number source).stk 11=[false] := ⟨rfl,rfl,rfl,rfl⟩

def terminal (roles : Stack ≃ Stack) (doubled : Bool) (background : Stack → List Bool)
    (context : C) (number : Nat) (source : List Bool) : State C :=
  let final:=finalState roles doubled background context number source
  ⟨none,final.var,final.stk⟩
theorem return_body (roles : Stack ≃ Stack) (doubled : Bool) : atProgram (C:=C) roles doubled 5=.halt := rfl
theorem return_halts (roles : Stack ≃ Stack) (doubled : Bool) (background : Stack → List Bool)
    (context : C) (number : Nat) (source : List Bool) :
    TM2.step (atProgram roles doubled) (finalState roles doubled background context number source)=
      some (terminal roles doubled background context number source) := rfl
theorem terminal_halt (roles : Stack ≃ Stack) (doubled : Bool) (background : Stack → List Bool)
    (context : C) (number : Nat) (source : List Bool) :
    TM2.step (atProgram roles doubled) (terminal roles doubled background context number source)=none := rfl

private theorem identity_statement (body : Statement C) : StackIso.statement (Equiv.refl Stack) body=body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => simp only [StackIso.statement,Equiv.refl_apply,ih]
  | branch _ _ _ yes no => simp only [StackIso.statement,yes,no]
  | goto _ | halt => rfl
private theorem identity_configuration (current : State C) : StackIso.configuration (Equiv.refl Stack) current=current := by
  cases current;rfl

theorem caller_chain {roles : Stack ≃ Stack} {doubled : Bool} {background : Stack → List Bool}
    {context : C} {memory : RatOutput.Store} {number : Nat} {source old10 old11 : List Bool} {trace : List (State C)}
    (facts : AtFacts roles doubled background context memory number source old10 old11 trace)
    (code : Label → Statement C) (same : ∀ point,point≠5→code point=atProgram roles doubled point) :
    trace.IsChain (fun a b => TM2.step code a=some b) := by
  have mapped:=StackIso.chain_configuration_on (Equiv.refl Stack) (atProgram roles doubled) code trace facts.chain
    (by
      intro current member point selected
      rw [identity_statement]
      apply same point
      intro equal
      subst point
      exact (facts.proper current member).1 selected)
  rw [List.map_id'' identity_configuration trace] at mapped
  exact mapped

end RootB234.RuntimeCounter.Builder.Public
