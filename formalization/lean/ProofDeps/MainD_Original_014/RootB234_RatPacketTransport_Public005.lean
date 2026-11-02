module
public import RootB234_RatPacketTransport_Rename004

/-! The three literal call sites requested by the original word loop.
The program, roles and mode are fixed independently of x and all tails.
Each actual returns at active port4, whose closed body really halts. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.RatPacketTransport.Public
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
variable {C : Type*}

def move15To2Roles : Stack ≃ Stack := Equiv.refl _
def copy2To13Roles : Stack ≃ Stack := (Equiv.swap 15 2).trans (Equiv.swap 15 13)
def move13To15Roles : Stack ≃ Stack := copy2To13Roles.symm

def move15To2 : Label → Statement C := atProgram move15To2Roles false
def copy2To13 : Label → Statement C := atProgram copy2To13Roles true
def move13To15 : Label → Statement C := atProgram move13To15Roles false

def physicalBank (source destination : Stack) (background : Stack → List Bool)
    (input temporary output : List Bool) : Stack → List Bool :=
  fun slot => if slot=source then input else if slot=4 then temporary
    else if slot=destination then output else background slot

def physicalState (source destination : Stack) (background : Stack → List Bool) (point : Label)
    (context : C) (memory : RatOutput.Store) (input temporary output : List Bool) : State C :=
  ⟨some point,(context,memory),physicalBank source destination background input temporary output⟩

theorem move15To2_state (background : Stack → List Bool) (point : Label)
    (context : C) (memory : RatOutput.Store) (input temporary output : List Bool) :
    atState move15To2Roles background point context memory input temporary output=
      physicalState 15 2 background point context memory input temporary output := rfl

theorem copy2To13_state (background : Stack → List Bool) (point : Label)
    (context : C) (memory : RatOutput.Store) (input temporary output : List Bool) :
    atState copy2To13Roles background point context memory input temporary output=
      physicalState 2 13 background point context memory input temporary output := rfl

theorem move13To15_state (background : Stack → List Bool) (point : Label)
    (context : C) (memory : RatOutput.Store) (input temporary output : List Bool) :
    atState move13To15Roles background point context memory input temporary output=
      physicalState 13 15 background point context memory input temporary output := rfl

theorem move15To2_actual (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (x : Rat) (oldSrc oldDst : List Bool) :
    ∃ trace,AtFacts move15To2Roles false background context memory x oldSrc oldDst trace :=
  at_actual _ _ _ _ _ _ _ _

theorem copy2To13_actual (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (x : Rat) (oldSrc oldDst : List Bool) :
    ∃ trace,AtFacts copy2To13Roles true background context memory x oldSrc oldDst trace :=
  at_actual _ _ _ _ _ _ _ _

theorem move13To15_actual (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (x : Rat) (oldSrc oldDst : List Bool) :
    ∃ trace,AtFacts move13To15Roles false background context memory x oldSrc oldDst trace :=
  at_actual _ _ _ _ _ _ _ _

theorem move15To2_supports : TM2.Supports (move15To2 (C:=C)) support := at_supports _ _
theorem copy2To13_supports : TM2.Supports (copy2To13 (C:=C)) support := at_supports _ _
theorem move13To15_supports : TM2.Supports (move13To15 (C:=C)) support := at_supports _ _

theorem move15To2_frame (slot : Stack) :
    ¬AtWork move15To2Roles slot ↔ slot≠15 ∧ slot≠4 ∧ slot≠2 := by
  simp only [AtWork,move15To2Roles,Equiv.refl_apply,not_or]

theorem copy2To13_frame (slot : Stack) :
    ¬AtWork copy2To13Roles slot ↔ slot≠2 ∧ slot≠4 ∧ slot≠13 := by
  change ¬(slot=2 ∨ slot=4 ∨ slot=13) ↔ _
  simp only [not_or]

theorem move13To15_frame (slot : Stack) :
    ¬AtWork move13To15Roles slot ↔ slot≠13 ∧ slot≠4 ∧ slot≠15 := by
  change ¬(slot=13 ∨ slot=4 ∨ slot=15) ↔ _
  simp only [not_or]

def terminal (roles : Stack ≃ Stack) (copy : Bool) (background : Stack → List Bool)
    (context : C) (x : Rat) (oldSrc oldDst : List Bool) : State C :=
  ⟨none,(context,(false,false)),atBank roles background
    (if copy then RatInput.Encoder.packet x oldSrc else oldSrc) [] (RatInput.Encoder.packet x oldDst)⟩

theorem return_halts (roles : Stack ≃ Stack) (copy : Bool) (background : Stack → List Bool)
    (context : C) (x : Rat) (oldSrc oldDst : List Bool) :
    TM2.step (atProgram roles copy)
      (atState roles background 4 context (false,false)
        (if copy then RatInput.Encoder.packet x oldSrc else oldSrc) [] (RatInput.Encoder.packet x oldDst))=
      some (terminal roles copy background context x oldSrc oldDst) := rfl

theorem terminal_halt (roles : Stack ≃ Stack) (copy : Bool) (background : Stack → List Bool)
    (context : C) (x : Rat) (oldSrc oldDst : List Bool) :
    TM2.step (atProgram roles copy) (terminal roles copy background context x oldSrc oldDst)=none := rfl

theorem return_body (roles : Stack ≃ Stack) (copy : Bool) : atProgram (C:=C) roles copy 4=.halt := rfl

private theorem identity_statement (body : Statement C) :
    StackIso.statement (Equiv.refl Stack) body=body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih =>
    simp only [StackIso.statement,Equiv.refl_apply,ih]
  | branch _ _ _ yes no => simp only [StackIso.statement,yes,no]
  | goto _ | halt => rfl

private theorem identity_configuration (current : State C) :
    StackIso.configuration (Equiv.refl Stack) current=current := by
  cases current;rfl

/-- The exact same path can be called with a statically replaced return
body. No earlier boundary executes port4. The arbitrary caller's own
resources are outside this packet operation. -/
theorem caller_chain {roles : Stack ≃ Stack} {copy : Bool} {background : Stack → List Bool}
    {context : C} {memory : RatOutput.Store} {x : Rat} {oldSrc oldDst : List Bool} {trace : List (State C)}
    (facts : AtFacts roles copy background context memory x oldSrc oldDst trace)
    (code : Label → Statement C)
    (same : ∀ point,point≠4→code point=atProgram roles copy point) :
    trace.IsChain (fun a b => TM2.step code a=some b) := by
  have mapped:=StackIso.chain_configuration_on (Equiv.refl Stack) (atProgram roles copy) code trace facts.chain
    (by
      intro current member point selected
      rw [identity_statement]
      apply same point
      intro equal
      subst point
      exact (facts.proper current member).1 selected)
  rw [List.map_id'' identity_configuration trace] at mapped
  exact mapped

end RootB234.RatPacketTransport.Public
