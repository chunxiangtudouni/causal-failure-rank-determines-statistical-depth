module

public import RootB234_PrepExponent_NatIncrement001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.NatIncrement
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open PSTRTMRawNat010
variable {C : Type*}

def Work (slot : Stack) : Prop := slot=3 ∨ slot=11
instance (slot : Stack) : Decidable (Work slot) := by unfold Work; infer_instance

theorem restore_body : restoreBody (C:=C)=
    .pop 3 RatDrop.capture (.branch (fun memory => memory.2.1)
      (.push 11 RatDrop.bit (.goto (fun _ => 3))) (.goto (fun _ => 4))) := rfl

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C:=C) .halt point) := by
  fin_cases point <;> simp [program,restore_body,StackIso.WritesOnly,Work]

theorem program_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point) ≤ 4 := by
  fin_cases point <;> norm_num [program,restore_body,ScannerClock.actions]

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point) ≤ 4 := by
  fin_cases point <;> norm_num [program,restore_body,AuxWorkspace.pushes]

theorem program_readonly (point : Label) :
    B23_4_RatWordPrep.RawGetter.Readonly (fun memory : Store C => memory.1) (program .halt point) := by
  fin_cases point
  all_goals
    dsimp only [program]
    try rw [restore_body]
    dsimp [B23_4_RatWordPrep.RawGetter.Readonly,RatDrop.capture]
    repeat' constructor
    all_goals (intros; rfl)

theorem step_context (before after : State C) (edge : TM2.step (program .halt) before=some after) :
    after.var.1=before.var.1 := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact B23_4_RatWordPrep.RawGetter.nodes_readonly (fun v : Store C => v.1) _ (program_readonly point) memory contents
        _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (trace : List (State C)) (before : State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b)) :
    ∀ current∈trace,current.var.1=before.var.1 := by
  induction trace generalizing before with
  | nil => simp
  | cons start rest ih =>
    have same : start=before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have same := List.mem_singleton.mp member
      subst current
      rfl
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      intro current member
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · exact (ih next rfl tailChain current later).trans (step_context before next edge)


theorem step_resources (before after : State C) (bound : Nat)
    (edge : TM2.step (program .halt) before=some after)
    (bounded : ∀ slot,(before.stk slot).length ≤ bound) :
    (∀ slot,(after.stk slot).length ≤ bound+4) ∧
      ∀ slot,¬Work slot→after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact ⟨fun slot => (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
        (Nat.add_le_add_left (program_pushes point) bound),
        fun slot untouched => StackIso.nodes_frame _ _ (program_writes point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)⟩

theorem trace_resources (trace : List (State C)) (before : State C) (background : RatInput.Stack → List Bool)
    (bound : Nat) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b))
    (bounded : ∀ slot,(before.stk slot).length ≤ bound)
    (frame : ∀ slot,¬Work slot→before.stk slot=background slot) :
    ∀ current∈trace,(∀ slot,(current.stk slot).length ≤ bound+4*trace.length) ∧
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
      · have tail := ih next (bound+4) rfl tailChain step.1
          (fun slot untouched => (step.2 slot untouched).trans (frame slot untouched)) current later
        refine ⟨?_,tail.2⟩
        intro slot
        have h := tail.1 slot
        simp only [List.length_cons] at h ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length ≤ bound) :
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      node.1.1=current.var.1 ∧ (∀ slot,(node.2 slot).length ≤ bound+4) ∧
        ∀ slot,¬Work slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk ≤ 8*(bound+5) := by
  refine ⟨?_,?_⟩
  · intro node member
    exact ⟨B23_4_RatWordPrep.RawGetter.nodes_readonly (fun v : Store C => v.1) _ (program_readonly point) current.var current.stk node member,
      fun slot => (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes point) bound),
      fun slot untouched => StackIso.nodes_frame _ _ (program_writes point) current.var current.stk slot untouched node member⟩
  · exact (ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))


def initialMass (background : Stack → List Bool) (number : Nat) (tail : List Bool) : Nat :=
  RatInput.occupied (bank background (B23_4_RatWordPrep.NatField.packet number tail) [])

def scale (background : Stack → List Bool) (number : Nat) (tail : List Bool) : Nat :=
  initialMass background number tail+1

theorem leftBlocks_length (digits : List Bool) : (leftBlocks digits).length=2*digits.length := by
  induction digits with
  | nil => rfl
  | cons bit later ih => simp [leftBlocks,List.flatMap_cons] at *; omega

theorem bits_le_initial (background : Stack → List Bool) (number : Nat) (tail : List Bool) :
    (PSTRTMNatValue017.rawPayload number).length ≤ initialMass background number tail := by
  have bound := RatInput.Encoder.point_mass
    (bank background (B23_4_RatWordPrep.NatField.packet number tail) []) 11
  change (B23_4_RatWordPrep.NatField.packet number tail).length ≤ initialMass background number tail at bound
  simp only [B23_4_RatWordPrep.NatField.packet,List.length_append,leftBlocks_length,List.length_cons] at bound
  omega

theorem actual_time (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (tail : List Bool) :
    (actualTrace background context memory (PSTRTMNatValue017.rawPayload number) tail []).length ≤ 
      3*scale background number tail := by
  have time := actual_length background context memory (PSTRTMNatValue017.rawPayload number) tail []
  have bound := bits_le_initial background number tail
  simp only [List.length_nil,Nat.add_zero] at time
  simp only [scale]
  omega

theorem actual_boundary (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (tail : List Bool) (current : State C)
    (member : current∈actualTrace background context memory (PSTRTMNatValue017.rawPayload number) tail []) :
    current.var.1=context ∧
      (∀ slot,(current.stk slot).length ≤ 13*scale background number tail) ∧
      ∀ slot,¬Work slot→current.stk slot=background slot := by
  let before := state background 0 context memory (B23_4_RatWordPrep.NatField.packet number tail) []
  let run := actualTrace background context memory (PSTRTMNatValue017.rawPayload number) tail []
  have head : run.head?=some before := actual_head _ _ _ _ _ _
  have chain := actual_chain (.halt : Statement C) background context memory
    (PSTRTMNatValue017.rawPayload number) tail []
  have ctx := trace_context run before head chain current member
  have bounds := trace_resources run before background (initialMass background number tail) head chain
    (RatInput.Encoder.point_mass before.stk) (by
      intro slot untouched
      simp only [Work,not_or] at untouched
      simp only [before,state,bank,untouched.2,untouched.1,ite_false]) current member
  refine ⟨ctx,?_,bounds.2⟩
  intro slot
  have cap := bounds.1 slot
  have time := actual_time background context memory number tail
  change run.length ≤ 3*scale background number tail at time
  simp only [scale] at time ⊢
  omega

theorem actual_internal (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (tail : List Bool) (current : State C)
    (member : current∈actualTrace background context memory (PSTRTMNatValue017.rawPayload number) tail [])
    (point : Label) (node : AuxWorkspace.Snapshot (Γ:=RatInput.Alphabet) (σ:=Store C))
    (inside : node∈AuxWorkspace.nodes (program .halt point) current.var current.stk) :
    node.1.1=context ∧ (∀ slot,(node.2 slot).length ≤ 17*scale background number tail) ∧
      (∀ slot,¬Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk ≤ 144*scale background number tail := by
  have boundary := actual_boundary background context memory number tail current member
  have nodes := internal_resources current point (13*scale background number tail) boundary.2.1
  have positive : 1 ≤ scale background number tail := by simp [scale]
  refine ⟨((nodes.1 node inside).1).trans boundary.1,?_,?_,?_⟩
  · intro slot
    have bounded := (nodes.1 node inside).2.1 slot
    omega
  · intro slot untouched
    exact ((nodes.1 node inside).2.2 slot untouched).trans (boundary.2.2 slot untouched)
  · exact nodes.2.trans (by omega)

def statementClock (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program .halt point) current.var current.stk

def traceClockSum (run : List (State C)) : Nat := (run.dropLast.map statementClock).sum

theorem actual_clock_sum (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (tail : List Bool) :
    traceClockSum (actualTrace background context memory (PSTRTMNatValue017.rawPayload number) tail []) ≤ 
      432*(scale background number tail)^2 := by
  let run := actualTrace background context memory (PSTRTMNatValue017.rawPayload number) tail []
  let S := scale background number tail
  have terms : ∀ n∈run.dropLast.map statementClock,n ≤ 144*S := by
    intro n member
    obtain ⟨current,present,rfl⟩ := List.mem_map.mp member
    have boundary := actual_boundary background context memory number tail current (List.dropLast_subset run present)
    have positive : 1 ≤ S := by simp [S,scale]
    cases selected : current.l with
    | none => simp [statementClock,selected]
    | some point =>
        simp only [statementClock,selected]
        have clocks := (internal_resources current point (13*S) boundary.2.1).2
        exact clocks.trans (by omega)
  have total : traceClockSum run ≤ run.dropLast.length*(144*S) := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (run.dropLast.map statementClock) (144*S) terms
  have count : run.dropLast.length ≤ 3*S := by
    rw [List.length_dropLast]
    exact (Nat.sub_le run.length 1).trans (actual_time background context memory number tail)
  exact total.trans ((Nat.mul_le_mul_right _ count).trans_eq (by ring))

end RootB234.PrepExponent.NatIncrement
