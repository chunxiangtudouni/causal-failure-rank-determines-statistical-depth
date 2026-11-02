module
public import RootB234_RuntimeCounter_Builder_Run002
public import RootB234_RatPacketTransport_Resources003

/-! Four static cell loops. Their paths are the frozen Builder clear10 and
PacketTransport reverse paths with fixed stack-role isomorphisms. A failed
Option pop returns to an ACTIVE label; FALSE cells are ordinary data. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.Cells
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

inductive Operation where
  | clear0 | clear1 | reverse13To3 | reverse3To2
  deriving DecidableEq

def moving : Operation → Bool
  | .clear0 | .clear1 => false
  | .reverse13To3 | .reverse3To2 => true
def roles : Operation → Stack ≃ Stack
  | .clear0 => Equiv.swap 10 0
  | .clear1 => Equiv.swap 10 1
  | .reverse13To3 => (Equiv.swap 4 13).trans (Equiv.swap 2 3)
  | .reverse3To2 => Equiv.swap 4 3
def entry (op : Operation) : Label := if moving op then 3 else 0
def returnPort (op : Operation) : Label := if moving op then 4 else 6
def source (op : Operation) : Stack := roles op (if moving op then 4 else 10)
def destination (op : Operation) : Stack := roles op 2

def rawProgram (move : Bool) : Label → Statement C :=
  if move then RatPacketTransport.program false .halt else RuntimeCounter.Builder.program false .halt
def rawEntry (move : Bool) : Label := if move then 3 else 0
def rawReturn (move : Bool) : Label := if move then 4 else 6
def body (op : Operation) : Statement C :=
  StackIso.statement (roles op) (rawProgram (moving op) (entry op))
def program (op : Operation) (caller : Statement C) (point : Label) : Statement C :=
  if point=entry op then body op else caller

def output (op : Operation) (before : Stack → List Bool) : Stack → List Bool :=
  if moving op then Function.update (Function.update before (source op) []) (destination op)
    ((before (source op)).reverse++before (destination op))
  else Function.update before (source op) []
def initial (op : Operation) (memory : Store C) (before : Stack → List Bool) : State C :=
  ⟨some (entry op),memory,before⟩
def result (op : Operation) (context : C) (before : Stack → List Bool) : State C :=
  ⟨some (returnPort op),(context,false,false),output op before⟩

def rawOutput (move : Bool) (before : Stack → List Bool) : Stack → List Bool :=
  if move then Function.update (Function.update before 4 []) 2 ((before 4).reverse++before 2)
  else Function.update before 10 []
def rawTrace (move : Bool) (context : C) (memory : RatOutput.Store) (before : Stack → List Bool) : List (State C) :=
  if move then RatPacketTransport.reverseTrace false before context (before 4) memory (before 15) (before 2)
  else RuntimeCounter.Builder.clear10Trace before context (before 8) (before 4) (before 11) (before 10) memory

private theorem clear_state (before : Stack → List Bool) (point : Label) (context : C)
    (memory : RatOutput.Store) (old : List Bool) :
    RuntimeCounter.Builder.state before point context memory (before 8) (before 4) old (before 11)=
      (⟨some point,(context,memory),Function.update before 10 old⟩ : State C) := by
  unfold RuntimeCounter.Builder.state
  congr 1
  funext slot
  fin_cases slot <;> rfl

private theorem reverse_state (before : Stack → List Bool) (point : Label) (context : C)
    (memory : RatOutput.Store) (old target : List Bool) :
    RatPacketTransport.state before point context memory (before 15) old target=
      (⟨some point,(context,memory),Function.update (Function.update before 4 old) 2 target⟩ : State C) := by
  unfold RatPacketTransport.state
  congr 1
  funext slot
  fin_cases slot <;> rfl

private theorem clear_proper (before : Stack → List Bool) (context : C)
    (input temporary leftguard old : List Bool) (memory : RatOutput.Store) :
    ∀ current∈(RuntimeCounter.Builder.clear10Trace before context input temporary leftguard old memory).dropLast,
      current.l=some 0 := by
  induction old generalizing memory with
  | nil => simp [RuntimeCounter.Builder.clear10Trace,RuntimeCounter.Builder.state]
  | cons bit later ih =>
    rw [RuntimeCounter.Builder.clear10Trace,List.dropLast_cons_of_ne_nil
      (by cases later <;> simp [RuntimeCounter.Builder.clear10Trace])]
    intro current member
    rcases List.mem_cons.mp member with rfl | rest
    · rfl
    · exact ih (true,bit) current rest

private theorem reverse_proper (before : Stack → List Bool) (context : C)
    (old : List Bool) (memory : RatOutput.Store) (input target : List Bool) :
    ∀ current∈(RatPacketTransport.reverseTrace false before context old memory input target).dropLast,
      current.l=some 3 := by
  induction old generalizing memory target with
  | nil => simp [RatPacketTransport.reverseTrace,RatPacketTransport.state]
  | cons bit later ih =>
    rw [RatPacketTransport.reverseTrace,List.dropLast_cons_of_ne_nil (RatPacketTransport.reverse_nonempty _ _ _ _ _ _ _)]
    intro current member
    rcases List.mem_cons.mp member with rfl | rest
    · rfl
    · exact ih (true,bit) (bit::target) current rest

theorem raw_head (move : Bool) (context : C) (memory : RatOutput.Store) (before : Stack → List Bool) :
    (rawTrace move context memory before).head?=some (⟨some (rawEntry move),(context,memory),before⟩ : State C) := by
  cases move
  · change (RuntimeCounter.Builder.clear10Trace before context (before 8) (before 4) (before 11) (before 10) memory).head?=_
    rw [RuntimeCounter.Builder.clear10_head,clear_state,Function.update_eq_self]
    rfl
  · change (RatPacketTransport.reverseTrace false before context (before 4) memory (before 15) (before 2)).head?=_
    rw [RatPacketTransport.reverse_head,reverse_state,Function.update_eq_self,Function.update_eq_self]
    rfl

theorem raw_last (move : Bool) (context : C) (memory : RatOutput.Store) (before : Stack → List Bool) :
    (rawTrace move context memory before).getLast?=
      some (⟨some (rawReturn move),(context,false,false),rawOutput move before⟩ : State C) := by
  cases move
  · change (RuntimeCounter.Builder.clear10Trace before context (before 8) (before 4) (before 11) (before 10) memory).getLast?=_
    rw [RuntimeCounter.Builder.clear10_last,clear_state]
    rfl
  · change (RatPacketTransport.reverseTrace false before context (before 4) memory (before 15) (before 2)).getLast?=_
    simpa only [rawReturn,rawOutput,ite_true,Bool.false_eq_true,ite_false,reverse_state] using
      RatPacketTransport.reverse_last false before context (before 4) memory (before 15) (before 2)

theorem raw_chain (move : Bool) (context : C) (memory : RatOutput.Store) (before : Stack → List Bool) :
    (rawTrace move context memory before).IsChain (fun a b => TM2.step (rawProgram move) a=some b) := by
  cases move
  · exact RuntimeCounter.Builder.clear10_chain false .halt before context (before 8) (before 4) (before 11) (before 10) memory
  · exact RatPacketTransport.reverse_chain false .halt before context (before 4) memory (before 15) (before 2)

theorem raw_length (move : Bool) (context : C) (memory : RatOutput.Store) (before : Stack → List Bool) :
    (rawTrace move context memory before).length=(before (if move then 4 else 10)).length+2 := by
  cases move
  · exact RuntimeCounter.Builder.clear10_length before context (before 8) (before 4) (before 11) (before 10) memory
  · exact RatPacketTransport.reverse_length false before context (before 4) memory (before 15) (before 2)

theorem raw_proper (move : Bool) (context : C) (memory : RatOutput.Store) (before : Stack → List Bool) :
    ∀ current∈(rawTrace move context memory before).dropLast,current.l=some (rawEntry move) := by
  cases move
  · exact clear_proper before context (before 8) (before 4) (before 11) (before 10) memory
  · exact reverse_proper before context (before 4) memory (before 15) (before 2)

theorem slots_inverse (rename : Stack ≃ Stack) (before : Stack → List Bool) :
    StackIso.slots rename (StackIso.slots rename.symm before)=before := by
  funext slot
  simp only [StackIso.slots,Equiv.symm_symm,Equiv.apply_symm_apply]

theorem output_renamed (op : Operation) (before : Stack → List Bool) :
    StackIso.slots (roles op) (rawOutput (moving op) (StackIso.slots (roles op).symm before))=output op before := by
  cases selected : moving op <;>
    simp only [rawOutput,output,source,destination,selected,Bool.false_eq_true,ite_false,ite_true,
      StackIso.slots_update,slots_inverse,StackIso.slots,Equiv.symm_symm]

def trace (op : Operation) (memory : Store C) (before : Stack → List Bool) : List (State C) :=
  (rawTrace (moving op) memory.1 memory.2 (StackIso.slots (roles op).symm before)).map
    (StackIso.configuration (roles op))

theorem trace_head (op : Operation) (memory : Store C) (before : Stack → List Bool) :
    (trace op memory before).head?=some (initial op memory before) := by
  rw [trace,List.head?_map,raw_head,Option.map_some]
  simp only [StackIso.configuration,slots_inverse,initial,entry,rawEntry,Prod.eta]

theorem trace_last (op : Operation) (memory : Store C) (before : Stack → List Bool) :
    (trace op memory before).getLast?=some (result op memory.1 before) := by
  rw [trace,List.getLast?_map,raw_last,Option.map_some]
  simp only [StackIso.configuration,output_renamed,result,returnPort,rawReturn]

theorem trace_length (op : Operation) (memory : Store C) (before : Stack → List Bool) :
    (trace op memory before).length=(before (source op)).length+2 := by
  rw [trace,List.length_map,raw_length]
  rfl

theorem trace_proper (op : Operation) (memory : Store C) (before : Stack → List Bool) :
    ∀ current∈(trace op memory before).dropLast,current.l=some (entry op) := by
  intro current member
  rw [trace,←List.map_dropLast] at member
  obtain ⟨old,present,rfl⟩:=List.mem_map.mp member
  exact raw_proper _ _ _ _ old present

theorem trace_chain (op : Operation) (caller : Statement C) (memory : Store C) (before : Stack → List Bool) :
    (trace op memory before).IsChain (fun a b => TM2.step (program op caller) a=some b) := by
  apply StackIso.chain_configuration_on (roles op) (rawProgram (moving op)) (program op caller) _ (raw_chain _ _ _ _)
  intro current member point selected
  have active:=raw_proper _ _ _ _ current member
  have equal : point=entry op := Option.some.inj (selected.symm.trans active)
  subst point
  simp only [program,ite_true,body]

def support : Finset Label := Finset.univ
private theorem supports_stmt (statement : Statement C) : TM2.SupportsStmt support statement := by
  induction statement with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _;exact Finset.mem_univ _
  | halt => trivial
theorem supports (op : Operation) (caller : Statement C) : TM2.Supports (program op caller) support :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩
theorem return_ne_entry (op : Operation) : returnPort op≠entry op := by cases op <;> decide
theorem return_body (op : Operation) (caller : Statement C) : program op caller (returnPort op)=caller :=
  by simp only [program,return_ne_entry,ite_false]

end RootB234.Cells
