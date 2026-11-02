module
public import RootB234_RatPacketTransport_Public005
public import B23_4_RatWordPrep_SeqCmp_NatFieldCurrent_052

/-! A finite physical Nat-packet COPY and counter builder. Real EOF reads
clear arbitrary old10/11. The source packet is restored through temporary4;
every counter cell, both00 guards, markerTRUE and leftguardFALSE is pushed.
The mode is selected statically, independently of the number and all widths. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.RuntimeCounter.Builder
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRTMRawNat010
abbrev Stack := RatInput.Stack
abbrev Label := RatDrop.Label
abbrev Store (C : Type*) := C×RatOutput.Store
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)
abbrev Path {C : Type*} := RatPacketTransport.Path (C:=C)
variable {C : Type*}

def roles : Stack ≃ Stack := (Equiv.swap 15 8).trans (Equiv.swap 3 4)

def eraseBody (slot : Stack) (again next : Label) : Statement C :=
  .pop slot RatDrop.capture (.branch (fun memory => memory.2.1)
    (.goto (fun _ => again)) (.goto (fun _ => next)))

def padBody (doubled : Bool) : Statement C :=
  if doubled then .push 10 (fun _ => true) (.push 10 (fun _ => false) (.goto (fun _ => 5)))
  else .goto (fun _ => 5)

def program (doubled : Bool) (caller : Statement C) (point : Label) : Statement C :=
  match point.val with
  | 0 => eraseBody 10 0 6
  | 1 => StackIso.statement roles (RatDrop.fieldBody true 1 2)
  | 2 => .pop 4 RatDrop.capture (.push 8 RatDrop.bit
      (.pop 4 RatDrop.capture (.push 8 RatDrop.bit (.goto (fun _ => 3)))))
  | 3 => .pop 4 RatDrop.capture (.branch (fun memory => memory.2.1)
      (.push 10 (fun _ => true) (.push 10 RatDrop.bit (.push 8 RatDrop.bit
        (.pop 4 RatDrop.capture (.push 8 RatDrop.bit (.goto (fun _ => 3)))))))
      (.goto (fun _ => 4)))
  | 4 => padBody doubled
  | 6 => eraseBody 11 6 7
  | 7 => .push 10 (fun _ => true) (.push 10 (fun _ => false) (.push 10 (fun _ => false)
      (.push 11 (fun _ => false) (.goto (fun _ => 1)))))
  | _ => caller

def bank (background : Stack → List Bool) (source temporary counter leftguard : List Bool) : Stack → List Bool :=
  fun slot => if slot=8 then source else if slot=4 then temporary else if slot=10 then counter
    else if slot=11 then leftguard else background slot

def state (background : Stack → List Bool) (point : Label) (context : C) (memory : RatOutput.Store)
    (source temporary counter leftguard : List Bool) : State C :=
  ⟨some point,(context,memory),bank background source temporary counter leftguard⟩

theorem update_source (background : Stack → List Bool) (source temporary counter leftguard next : List Bool) :
    Function.update (bank background source temporary counter leftguard) 8 next=bank background next temporary counter leftguard := by
  funext slot;fin_cases slot <;> rfl
theorem update_temporary (background : Stack → List Bool) (source temporary counter leftguard next : List Bool) :
    Function.update (bank background source temporary counter leftguard) 4 next=bank background source next counter leftguard := by
  funext slot;fin_cases slot <;> rfl
theorem update_counter (background : Stack → List Bool) (source temporary counter leftguard next : List Bool) :
    Function.update (bank background source temporary counter leftguard) 10 next=bank background source temporary next leftguard := by
  funext slot;fin_cases slot <;> rfl
theorem update_guard (background : Stack → List Bool) (source temporary counter leftguard next : List Bool) :
    Function.update (bank background source temporary counter leftguard) 11 next=bank background source temporary counter next := by
  funext slot;fin_cases slot <;> rfl

def oldBackground (background : Stack → List Bool) (counter leftguard : List Bool) : Stack → List Bool :=
  StackIso.slots roles.symm (bank background [] [] counter leftguard)

theorem renamed_state (background : Stack → List Bool) (point : Label) (context : C)
    (memory : RatOutput.Store) (source temporary counter leftguard : List Bool) :
    StackIso.configuration roles (RatDrop.state (oldBackground background counter leftguard) point context memory source temporary)=
      state background point context memory source temporary counter leftguard := by
  unfold StackIso.configuration StackIso.slots RatDrop.state RatDrop.cells oldBackground state bank
  congr 1
  funext slot;fin_cases slot <;> rfl

theorem field_chain (doubled : Bool) (caller : Statement C) (background : Stack → List Bool)
    (context : C) (digits : List Bool) (memory : RatOutput.Store) (source temporary : List Bool)
    (counter leftguard : List Bool) :
    ((RatDrop.fieldTrace true (oldBackground background counter leftguard) context 1 2 digits memory source temporary).map
      (StackIso.configuration roles)).IsChain (fun a b => TM2.step (program doubled caller) a=some b) := by
  apply StackIso.chain_configuration_on roles (RatDrop.program .halt) (program doubled caller) _
    (RatDrop.field_chain .halt true _ context 1 2 rfl digits memory source temporary)
  intro current member point selected
  have label:=RatPacketTransport.field_proper _ context 1 2 digits memory source temporary current member
  have same : point=1 := Option.some.inj (selected.symm.trans label)
  subst point;rfl

theorem clear10_bit (doubled : Bool) (caller : Statement C) (background : Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (bit : Bool) (source temporary counter leftguard : List Bool) :
    TM2.step (program doubled caller) (state background 0 context memory source temporary (bit::counter) leftguard)=
      some (state background 0 context (true,bit) source temporary counter leftguard) := by
  simp [program,eraseBody,state,TM2.step,TM2.stepAux,RatDrop.capture,bank,update_counter]

theorem clear10_end (doubled : Bool) (caller : Statement C) (background : Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (source temporary leftguard : List Bool) :
    TM2.step (program doubled caller) (state background 0 context memory source temporary [] leftguard)=
      some (state background 6 context (false,false) source temporary [] leftguard) := by
  simp [program,eraseBody,state,TM2.step,TM2.stepAux,RatDrop.capture,bank,update_counter]

theorem clear11_bit (doubled : Bool) (caller : Statement C) (background : Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (bit : Bool) (source temporary counter leftguard : List Bool) :
    TM2.step (program doubled caller) (state background 6 context memory source temporary counter (bit::leftguard))=
      some (state background 6 context (true,bit) source temporary counter leftguard) := by
  simp [program,eraseBody,state,TM2.step,TM2.stepAux,RatDrop.capture,bank,update_guard]

theorem clear11_end (doubled : Bool) (caller : Statement C) (background : Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (source temporary counter : List Bool) :
    TM2.step (program doubled caller) (state background 6 context memory source temporary counter [])=
      some (state background 7 context (false,false) source temporary counter []) := by
  simp [program,eraseBody,state,TM2.step,TM2.stepAux,RatDrop.capture,bank,update_guard]

theorem seed_step (doubled : Bool) (caller : Statement C) (background : Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (source temporary : List Bool) :
    TM2.step (program doubled caller) (state background 7 context memory source temporary [] [])=
      some (state background 1 context memory source temporary [false,false,true] [false]) := by
  simp [program,state,TM2.step,TM2.stepAux,bank,update_counter,update_guard]

theorem restore_guards (doubled : Bool) (caller : Statement C) (background : Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (source temporary counter leftguard : List Bool) :
    TM2.step (program doubled caller) (state background 2 context memory source (false::false::temporary) counter leftguard)=
      some (state background 3 context (true,false) (false::false::source) temporary counter leftguard) := by
  simp [program,state,TM2.step,TM2.stepAux,RatDrop.capture,RatDrop.bit,bank,update_source,update_temporary]

theorem reverse_bit (doubled : Bool) (caller : Statement C) (background : Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (bit : Bool) (source temporary counter leftguard : List Bool) :
    TM2.step (program doubled caller) (state background 3 context memory source (bit::true::temporary) counter leftguard)=
      some (state background 3 context (true,true) (true::bit::source) temporary (bit::true::counter) leftguard) := by
  simp [program,state,TM2.step,TM2.stepAux,RatDrop.capture,RatDrop.bit,bank,update_source,update_temporary,update_counter]

theorem reverse_end (doubled : Bool) (caller : Statement C) (background : Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (source counter leftguard : List Bool) :
    TM2.step (program doubled caller) (state background 3 context memory source [] counter leftguard)=
      some (state background 4 context (false,false) source [] counter leftguard) := by
  simp [program,state,TM2.step,TM2.stepAux,RatDrop.capture,bank,update_temporary]

def selectDigits (doubled : Bool) (digits : List Bool) : List Bool := if doubled then false::digits else digits

theorem pad_step (doubled : Bool) (caller : Statement C) (background : Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (digits source leftguard : List Bool) :
    TM2.step (program doubled caller)
      (state background 4 context memory source [] (PSTRTMIncrement009.blocks digits++[false,false,true]) leftguard)=
      some (state background 5 context memory source []
        (PSTRTMIncrement009.blocks (selectDigits doubled digits)++[false,false,true]) leftguard) := by
  cases doubled <;> simp [program,padBody,state,TM2.step,TM2.stepAux,selectDigits,
    PSTRTMIncrement009.blocks,bank,update_counter]

end RootB234.RuntimeCounter.Builder
