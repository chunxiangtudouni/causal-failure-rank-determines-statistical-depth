module
public import B23_4_RatWordPrep_SeqCmp_RawWidth_031
public import PSTR_WordBool_RatDrop_Packet_004

/-! Fixed packet transport, reusing the frozen RatDrop two-00 parser.
The actual parser's old parking role3 is statically renamed to temporary4.
The only new loop returns the finitely parked cells to2 and optionally15. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.RatPacketTransport
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

abbrev Stack := RatInput.Stack
abbrev Label := RatDrop.Label
abbrev Store (C : Type*) := C × RatOutput.Store
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)
variable {C : Type*}

def roles : Stack ≃ Stack := Equiv.swap 3 4

def keepSource (copy : Bool) (next : Statement C) : Statement C :=
  if copy then .push 15 RatDrop.bit next else next

def program (copy : Bool) (caller : Statement C) (point : Label) : Statement C :=
  match point.val with
  | 0 => StackIso.statement roles (RatDrop.headerBody true 1)
  | 1 => StackIso.statement roles (RatDrop.fieldBody true 1 2)
  | 2 => StackIso.statement roles (RatDrop.fieldBody true 2 3)
  | 3 => .pop 4 RatDrop.capture (.branch (fun memory => memory.2.1)
      (keepSource copy (.push 2 RatDrop.bit (.goto (fun _ => 3)))) (.goto (fun _ => 4)))
  | _ => caller

def bank (background : Stack → List Bool) (source temporary target : List Bool) : Stack → List Bool :=
  fun point => if point=15 then source else if point=4 then temporary else if point=2 then target else background point

def state (background : Stack → List Bool) (point : Label) (context : C) (memory : RatOutput.Store)
    (source temporary target : List Bool) : State C :=
  ⟨some point,(context,memory),bank background source temporary target⟩

def oldBackground (background : Stack → List Bool) (target : List Bool) : Stack → List Bool :=
  StackIso.slots roles.symm (Function.update background 2 target)

theorem renamed_state (background : Stack → List Bool) (point : Label) (context : C)
    (memory : RatOutput.Store) (source temporary target : List Bool) :
    StackIso.configuration roles (RatDrop.state (oldBackground background target) point context memory source temporary)=
      state background point context memory source temporary target := by
  unfold StackIso.configuration StackIso.slots RatDrop.state RatDrop.cells oldBackground state bank
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem program_parse (copy : Bool) (caller : Statement C) (point : Label) (small : point.val<3) :
    program copy caller point=StackIso.statement roles (RatDrop.program .halt point) := by
  fin_cases point <;> norm_num at small <;> rfl

theorem field_proper (background : Stack → List Bool) (context : C) (point next : Label)
    (digits : List Bool) (memory : RatOutput.Store) (source temporary : List Bool) :
    ∀ current∈(RatDrop.fieldTrace true background context point next digits memory source temporary).dropLast,
      current.l=some point := by
  induction digits generalizing memory temporary with
  | nil => simp [RatDrop.fieldTrace,RatDrop.state]
  | cons digit later ih =>
    rw [RatDrop.fieldTrace,List.dropLast_cons_of_ne_nil (RatDrop.field_nonempty _ _ _ _ _ _ _ _ _)]
    intro current member
    rcases List.mem_cons.mp member with rfl | rest
    · rfl
    · exact ih (true,digit) (digit::true::temporary) current rest

theorem field_chain (copy : Bool) (caller : Statement C) (background : Stack → List Bool)
    (context : C) (point next : Label) (small : point.val<3)
    (oldCode : RatDrop.program (.halt : RatDrop.Statement C) point=RatDrop.fieldBody true point next)
    (digits : List Bool) (memory : RatOutput.Store) (source temporary : List Bool) :
    ((RatDrop.fieldTrace true background context point next digits memory source temporary).map
      (StackIso.configuration roles)).IsChain (fun a b => TM2.step (program copy caller) a=some b) := by
  apply StackIso.chain_configuration_on roles (RatDrop.program .halt) (program copy caller)
    _ (RatDrop.field_chain .halt true background context point next oldCode digits memory source temporary)
  intro current member q selected
  have active := field_proper background context point next digits memory source temporary current member
  have equal : q=point := Option.some.inj (selected.symm.trans active)
  subst q
  exact program_parse copy caller point small

theorem update_source (background : Stack → List Bool) (source temporary target replacement : List Bool) :
    Function.update (bank background source temporary target) 15 replacement=bank background replacement temporary target := by
  funext slot;fin_cases slot <;> rfl

theorem update_temporary (background : Stack → List Bool) (source temporary target replacement : List Bool) :
    Function.update (bank background source temporary target) 4 replacement=bank background source replacement target := by
  funext slot;fin_cases slot <;> rfl

theorem update_target (background : Stack → List Bool) (source temporary target replacement : List Bool) :
    Function.update (bank background source temporary target) 2 replacement=bank background source temporary replacement := by
  funext slot;fin_cases slot <;> rfl

theorem reverse_bit (copy : Bool) (caller : Statement C) (background : Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (bit : Bool) (source temporary target : List Bool) :
    TM2.step (program copy caller) (state background 3 context memory source (bit::temporary) target)=
      some (state background 3 context (true,bit) (if copy then bit::source else source) temporary (bit::target)) := by
  cases copy <;> simp [state,program,keepSource,TM2.step,TM2.stepAux,RatDrop.capture,RatDrop.bit,
    bank,update_source,update_temporary,update_target]

theorem reverse_end (copy : Bool) (caller : Statement C) (background : Stack → List Bool)
    (context : C) (memory : RatOutput.Store) (source target : List Bool) :
    TM2.step (program copy caller) (state background 3 context memory source [] target)=
      some (state background 4 context (false,false) source [] target) := by
  simp [state,program,TM2.step,TM2.stepAux,RatDrop.capture,bank,update_temporary]

end RootB234.RatPacketTransport
