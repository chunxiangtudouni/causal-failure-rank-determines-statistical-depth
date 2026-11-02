module

public import RootB234_PrepEntry_NatPacketRun_079

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.NatPacket

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*}

variable {copy : Bool}

theorem step_context (before after : State C) (edge : TM2.step (program copy .halt) before=some after) :
    Prod.fst after.var=Prod.fst before.var := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program copy .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact RawGetter.nodes_readonly Prod.fst _ (program_readonly copy point) memory contents _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (trace : List (State C)) (before : State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program copy .halt) a=some b)) :
    ∀ current∈trace,Prod.fst current.var=Prod.fst before.var := by
  induction trace generalizing before with
  | nil => simp
  | cons start rest ih =>
    have same : start=before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have same:=List.mem_singleton.mp member
      subst current
      rfl
    | cons next rest =>
      obtain ⟨edge,tailChain⟩:=List.isChain_cons_cons.mp chain
      intro current member
      rcases List.mem_cons.mp member with rfl|later
      · rfl
      · exact (ih next rfl tailChain current later).trans (step_context before next edge)


theorem step_resources (before after : State C) (bound : Nat)
    (edge : TM2.step (program copy .halt) before=some after)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    (∀ slot,(after.stk slot).length≤bound+2) ∧
      ∀ slot,¬Work slot→after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program copy .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact ⟨fun slot => (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
        (Nat.add_le_add_left (program_pushes copy point) bound),
        fun slot untouched => StackIso.nodes_frame _ _ (program_writes copy point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)⟩

theorem trace_resources (trace : List (State C)) (before : State C) (background : RatInput.Stack → List Bool)
    (bound : Nat) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program copy .halt) a=some b))
    (bounded : ∀ slot,(before.stk slot).length≤bound)
    (frame : ∀ slot,¬Work slot→before.stk slot=background slot) :
    ∀ current∈trace,(∀ slot,(current.stk slot).length≤bound+2*trace.length) ∧
      ∀ slot,¬Work slot→current.stk slot=background slot := by
  induction trace generalizing before bound with
  | nil => simp
  | cons firstState rest ih =>
    have same : firstState=before := Option.some.inj first
    subst firstState
    cases rest with
    | nil =>
      intro current member
      have same := List.mem_singleton.mp member
      subst current
      exact ⟨fun slot => (bounded slot).trans (by simp),frame⟩
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      have step := step_resources before next bound edge bounded
      intro current member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨fun slot => (bounded slot).trans (Nat.le_add_right _ _),frame⟩
      · have tail := ih next (bound+2) rfl tailChain step.1
          (fun slot untouched => (step.2 slot untouched).trans (frame slot untouched)) current later
        refine ⟨?_,tail.2⟩
        intro slot
        have h := tail.1 slot
        simp only [List.length_cons] at h ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length≤bound) :
    (∀ node∈AuxWorkspace.nodes (program copy .halt point) current.var current.stk,
      Prod.fst node.1=Prod.fst current.var ∧ (∀ slot,(node.2 slot).length≤bound+2) ∧
        ∀ slot,¬Work slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (program copy .halt point) current.var current.stk≤8*(bound+3) := by
  refine ⟨?_,?_⟩
  · intro node member
    exact ⟨RawGetter.nodes_readonly Prod.fst _ (program_readonly copy point) current.var current.stk node member,
      fun slot => (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes copy point) bound),
      fun slot untouched => StackIso.nodes_frame _ _ (program_writes copy point) current.var current.stk slot untouched node member⟩
  · exact (ScannerClock.clock_bound (program copy .halt point) current.var current.stk bound bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions copy point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes copy point) bound) 1))


def coefficient : Nat := 256

def mass (background : RatInput.Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (source target : List Bool) : Nat :=
  RatInput.occupied (entry background context memory number source target).stk

def scale (background : RatInput.Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (source target : List Bool) : Nat := mass background context memory number source target+1

theorem time_le (background : RatInput.Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (source target : List Bool) :
    3*(PSTRTMNatValue017.rawPayload number).length+6≤4*scale background context memory number source target := by
  have point:=RatInput.Encoder.point_mass (entry background context memory number source target).stk 15
  change (NatField.packet number source).length≤mass background context memory number source target at point
  rw [packet_length] at point
  dsimp only [scale]
  omega

theorem resource_envelope (occupied : Nat) :
    4*(occupied+1)≤coefficient*(occupied+1) ∧
    16*(occupied+2*(4*(occupied+1)))≤coefficient*(occupied+1) ∧
    16*(occupied+2*(4*(occupied+1))+2)≤coefficient*(occupied+1) ∧
    8*(occupied+2*(4*(occupied+1))+3)≤coefficient*(occupied+1) := by
  dsimp only [coefficient]
  omega

end RootB234.PrepEntry.NatPacket
