module

public import RootB234_WordFinalizer_Run_002

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.WordFinalizer

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PSTRWordVM

variable {C : Type*}

def Work (slot : Stack) : Prop := slot=0 ∨ slot=3 ∨ slot=13

theorem program_actions (point : Label) : ScannerClock.actions (program (C := C) point)≤2 := by
  cases point <;> exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C := C) point)≤1 := by
  cases point <;> exact of_decide_eq_true rfl

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C := C) point) := by
  cases point <;>
    simp [program,ContextLift.machine,ContextLift.statement,baseProgram,StackIso.WritesOnly,Work]

/-- Every syntax snapshot preserves the caller context, including the
snapshot after a successful or failed pop and before its selected branch. -/
theorem nodes_context (point : Label) (memory : Store C) (slots : Stack → List Bool)
    (node : AuxWorkspace.Snapshot (Γ := Alphabet) (σ := Store C))
    (member : node∈AuxWorkspace.nodes (program point) memory slots) : node.1.1=memory.1 := by
  rcases memory with ⟨context,registers⟩
  change node∈AuxWorkspace.nodes (ContextLift.statement (baseProgram point)) (context,registers) slots at member
  rw [ContextLift.nodes_configuration] at member
  obtain ⟨old,_present,same⟩ := List.mem_map.mp member
  subst node
  rfl

theorem program_nodes (point : Label) (memory : Store C) (slots : Stack → List Bool) :
    (AuxWorkspace.nodes (program point) memory slots).length≤4 := by
  cases point <;>
    simp only [program,ContextLift.machine,ContextLift.statement,baseProgram,AuxWorkspace.nodes,
      List.length_cons]
  all_goals split <;> simp

theorem step_resources (before after : State C) (bound : Nat)
    (edge : TM2.step program before=some after)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    (∀ slot,(after.stk slot).length≤bound+1) ∧ after.var.1=before.var.1 ∧
      ∀ slot,¬Work slot→after.stk slot=before.stk slot := by
  cases before with
  | mk position memory slots =>
    cases position with
    | none => cases edge
    | some point =>
      have equal : after=TM2.stepAux (program point) memory slots := (Option.some.inj edge).symm
      subst after
      refine ⟨?_,?_,?_⟩
      · intro slot
        exact (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
          (Nat.add_le_add_left (program_pushes point) bound)
      · exact nodes_context point memory slots _ (AuxWorkspace.endpoint_mem _ _ _)
      · intro slot untouched
        exact StackIso.nodes_frame Work _ (program_writes point) memory slots slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_resources (trace : List (State C)) (before : State C)
    (frame : Stack → List Bool) (bound : Nat)
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step program a=some b))
    (bounded : ∀ slot,(before.stk slot).length≤bound)
    (framed : ∀ slot,¬Work slot→before.stk slot=frame slot) :
    ∀ current∈trace,(∀ slot,(current.stk slot).length≤bound+trace.length) ∧
      current.var.1=before.var.1 ∧ ∀ slot,¬Work slot→current.stk slot=frame slot := by
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
      exact ⟨fun slot => (bounded slot).trans (by simp),rfl,framed⟩
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      have step := step_resources before next bound edge bounded
      intro current member
      rcases List.mem_cons.mp member with same | later
      · subst current
        exact ⟨fun slot => (bounded slot).trans (Nat.le_add_right _ _),rfl,framed⟩
      · have tail := ih next (bound+1) rfl tailChain step.1
          (fun slot untouched => (step.2.2 slot untouched).trans (framed slot untouched)) current later
        refine ⟨?_,tail.2.1.trans step.2.1,tail.2.2⟩
        intro slot
        have perSlot := tail.1 slot
        simp only [List.length_cons] at perSlot ⊢
        omega

def scale (frame : Stack → List Bool) (old bits : List Bool) : Nat :=
  old.length+bits.length+RatInput.occupied frame+1

theorem scale_pos (frame : Stack → List Bool) (old bits : List Bool) : 0<scale frame old bits := by
  dsimp only [scale]
  omega

theorem entry_bound (frame : Stack → List Bool) (memory : Store C) (old bits : List Bool) :
    ∀ slot,((entry frame memory old bits).stk slot).length≤scale frame old bits := by
  intro slot
  have point := RatInput.Encoder.point_mass frame slot
  dsimp only [entry,state,cells,scale]
  split_ifs <;> (try rw [List.length_nil]) <;> omega

theorem entry_frame (frame : Stack → List Bool) (memory : Store C) (old bits : List Bool)
    (slot : Stack) (untouched : ¬Work slot) : (entry frame memory old bits).stk slot=frame slot := by
  have not0 : slot≠0 := fun equal => untouched (Or.inl equal)
  have not3 : slot≠3 := fun equal => untouched (Or.inr (Or.inl equal))
  have not13 : slot≠13 := fun equal => untouched (Or.inr (Or.inr equal))
  exact frame_at frame old [] bits slot not0 not3 not13

structure Facts (source : Label → Statement C) (frame : Stack → List Bool) (memory : Store C)
    (old bits : List Bool) (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (entry frame memory old bits)
  chain : trace.IsChain (fun a b => TM2.step source a=some b)
  last : trace.getLast?=some final
  halted : final.l=none
  halt : TM2.step source final=none
  context : final.var.1=memory.1
  contents : final.stk=cells frame bits [] []
  time : trace.length≤4*scale frame old bits
  boundary : ∀ current∈trace,
    current.var.1=memory.1 ∧
    (∀ slot,(current.stk slot).length≤5*scale frame old bits) ∧
    RatInput.occupied current.stk≤80*scale frame old bits ∧
    ∀ slot,¬Work slot→current.stk slot=frame slot
  internal : ∀ current∈trace.dropLast,∀ point,current.l=some point→
    (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
      node.1.1=memory.1 ∧
      (∀ slot,(node.2 slot).length≤6*scale frame old bits) ∧
      RatInput.occupied node.2≤96*scale frame old bits ∧
      ∀ slot,¬Work slot→node.2 slot=frame slot) ∧
    (AuxWorkspace.nodes (source point) current.var current.stk).length≤4 ∧
    ScannerStatement.clock (source point) current.var current.stk≤28*scale frame old bits

/-- All resources are derived from the actual_run witness. The caller
supplies no path, bound, fuel, output answer, or internal-space premise. -/
theorem actual_polynomial (frame : Stack → List Bool) (memory : Store C) (old bits : List Bool) :
    ∃ trace final,Facts program frame memory old bits trace final := by
  obtain ⟨trace,first,chain,last,count⟩ := actual_run frame memory old bits
  have positive := scale_pos frame old bits
  have time : trace.length≤4*scale frame old bits := by
    dsimp only [scale]
    omega
  have resources := trace_resources trace (entry frame memory old bits) frame (scale frame old bits)
    first chain (entry_bound frame memory old bits) (entry_frame frame memory old bits)
  have bounded : ∀ current∈trace,∀ slot,(current.stk slot).length≤5*scale frame old bits := by
    intro current member slot
    have h := (resources current member).1 slot
    omega
  refine ⟨trace,result frame memory.1 bits,⟨first,chain,last,rfl,result_halt frame memory.1 bits,
    rfl,rfl,time,?_,?_⟩⟩
  · intro current member
    refine ⟨(resources current member).2.1,bounded current member,?_,(resources current member).2.2⟩
    have h := RatInput.Encoder.occupied_bound current.stk _ (bounded current member)
    omega
  · intro current member point _selected
    have present := List.mem_of_mem_dropLast member
    have currentBound := bounded current present
    refine ⟨?_,program_nodes point current.var current.stk,?_⟩
    · intro node internal
      have nodeBound : ∀ slot,(node.2 slot).length≤6*scale frame old bits := by
        intro slot
        have h := (AuxWorkspace.node_bound (program point) current.var current.stk _
          currentBound node internal slot).trans
            (Nat.add_le_add_left (program_pushes point) (5*scale frame old bits))
        omega
      refine ⟨(nodes_context point current.var current.stk node internal).trans
        (resources current present).2.1,nodeBound,?_,?_⟩
      · have h := RatInput.Encoder.occupied_bound node.2 _ nodeBound
        omega
      · intro slot untouched
        exact (StackIso.nodes_frame Work _ (program_writes point) current.var current.stk
          slot untouched node internal).trans ((resources current present).2.2 slot untouched)
    · have clock := ScannerClock.clock_bound (program point) current.var current.stk _ currentBound
      have cap := clock.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) (5*scale frame old bits)) 1))
      omega

end RootB234.WordFinalizer
