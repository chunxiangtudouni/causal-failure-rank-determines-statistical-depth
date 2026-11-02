module

public import RootL01_SymbolicSource_Unary_Meaning_022
public import RootL01_SymbolicSource_RatLeaf_Public_004

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootL01.SymbolicSource.Unary

open Turing
open PaperProofs.Common.Native
open PSTRWordVM PSTRWordBool

variable {C : Type*}

def Work (slot : Stack) : Prop := slot=3 ∨ slot=5 ∨ slot=6

theorem cells_frame (frame : Bank) (digits value work : List Bool) (slot : Stack)
    (untouched : ¬Work slot) : cells frame digits value work slot = frame slot := by
  have a : slot ≠ 3 := fun equal => untouched (Or.inl equal)
  have b : slot ≠ 5 := fun equal => untouched (Or.inr (Or.inl equal))
  have c : slot ≠ 6 := fun equal => untouched (Or.inr (Or.inr equal))
  simp only [cells,a,b,c,ite_false]

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C:=C) .halt point) := by
  cases point <;> simp [program,baseProgram,ContextLift.statement,StackIso.WritesOnly,Work]

theorem program_readonly (point : Label) :
    RatLeaf.Readonly (fun memory : Store C => memory.1) (program .halt point) := by
  cases point <;>
    dsimp [program,baseProgram,ContextLift.statement,RatLeaf.Readonly,captureBit,capturePresent]
  all_goals repeat' constructor
  all_goals (intros; rfl)

theorem step_context (before after : State C) (edge : TM2.step (program .halt) before = some after) :
    after.var.1 = before.var.1 := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after = TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact RatLeaf.nodes_readonly (fun value : Store C => value.1) _ (program_readonly point)
        memory contents _ (AuxWorkspace.endpoint_mem _ _ _)

theorem step_resources (before after : State C) (bound : Nat)
    (edge : TM2.step (program .halt) before = some after)
    (bounded : ∀ slot,(before.stk slot).length ≤ bound) :
    (∀ slot,(after.stk slot).length ≤ bound+2) ∧
      ∀ slot,¬Work slot → after.stk slot = before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after = TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      refine ⟨?_,?_⟩
      · intro slot
        exact (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
          (Nat.add_le_add_left (syntax_pushes point) bound)
      · intro slot untouched
        exact StackIso.nodes_frame Work _ (program_writes point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_resources (trace : List (State C)) (before : State C) (frame : Bank) (bound : Nat)
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a = some b))
    (bounded : ∀ slot,(before.stk slot).length ≤ bound)
    (frames : ∀ slot,¬Work slot → before.stk slot = frame slot) :
    ∀ current ∈ trace,current.var.1 = before.var.1 ∧
      (∀ slot,(current.stk slot).length ≤ bound+2*trace.length) ∧
      ∀ slot,¬Work slot → current.stk slot = frame slot := by
  induction trace generalizing before bound with
  | nil => simp
  | cons start rest ih =>
    have same : start = before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have same := List.mem_singleton.mp member
      subst current
      exact ⟨rfl,fun slot => (bounded slot).trans (by simp),frames⟩
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      have step := step_resources before next bound edge bounded
      have nextFrames : ∀ slot,¬Work slot → next.stk slot = frame slot :=
        fun slot untouched => (step.2 slot untouched).trans (frames slot untouched)
      intro current member
      rcases List.mem_cons.mp member with same | later
      · subst current
        exact ⟨rfl,fun slot => (bounded slot).trans (Nat.le_add_right _ _),frames⟩
      · have tail := ih next (bound+2) rfl tailChain step.1 nextFrames current later
        refine ⟨tail.1.trans (step_context before next edge),?_,tail.2.2⟩
        intro slot
        have perSlot := tail.2.1 slot
        simp only [List.length_cons] at perSlot ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length ≤ bound) :
    (∀ node ∈ AuxWorkspace.nodes (program .halt point) current.var current.stk,
      node.1.1 = current.var.1 ∧ (∀ slot,(node.2 slot).length ≤ bound+2) ∧
      ∀ slot,¬Work slot → node.2 slot = current.stk slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk ≤ 6*(bound+3) := by
  refine ⟨?_,?_⟩
  · intro node member
    refine ⟨RatLeaf.nodes_readonly _ _ (program_readonly point) _ _ node member,?_,?_⟩
    · intro slot
      exact (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (syntax_pushes point) bound)
    · intro slot untouched
      exact StackIso.nodes_frame Work _ (program_writes point) current.var current.stk slot untouched node member
  · have clock := ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded
    exact clock.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (syntax_actions point))
      (Nat.add_le_add_right (Nat.add_le_add_left (syntax_pushes point) bound) 1))

def entry (frame : Bank) (context : C) (memory : Registers) (digits : List Bool) (amount : Nat) : State C :=
  state frame .read context memory digits (unary amount) []

def final (frame : Bank) (context : C) (digits : List Bool) (amount : Nat) : State C :=
  state frame .done context (false,false) [] (unary (evaluate digits amount)) []

def mass (frame : Bank) (context : C) (memory : Registers) (digits : List Bool) (amount : Nat) : Nat :=
  RatInput.occupied (entry frame context memory digits amount).stk

def scale (frame : Bank) (context : C) (memory : Registers) (digits : List Bool) (amount : Nat) : Nat :=
  mass frame context memory digits amount+2*time digits amount

def charge (trace : List (State C)) : Nat :=
  trace.length+(trace.dropLast.map (fun current => match current.l with
    | none => 0
    | some point => ScannerStatement.clock (program .halt point) current.var current.stk)).sum

structure Facts (frame : Bank) (context : C) (memory : Registers) (digits : List Bool) (amount : Nat)
    (trace : List (State C)) : Prop where
  first : trace.head? = some (entry frame context memory digits amount)
  chain : trace.IsChain (fun a b => TM2.step (program .halt) a = some b)
  last : trace.getLast? = some (final frame context digits amount)
  count : trace.length ≤ time digits amount
  boundaries : ∀ current ∈ trace,current.var.1 = context ∧
    (∀ slot,(current.stk slot).length ≤ scale frame context memory digits amount) ∧
    RatInput.occupied current.stk ≤ 16*scale frame context memory digits amount ∧
    ∀ slot,¬Work slot → current.stk slot = frame slot
  proper : ∀ current ∈ trace.dropLast,current.l ≠ some .done ∧
    ∀ point,current.l = some point →
      (∀ node ∈ AuxWorkspace.nodes (program .halt point) current.var current.stk,
        node.1.1 = context ∧ RatInput.occupied node.2 ≤ 16*(scale frame context memory digits amount+2) ∧
        ∀ slot,¬Work slot → node.2 slot = frame slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk ≤
        6*(scale frame context memory digits amount+3)

theorem actual_bounded (frame : Bank) (context : C) (memory : Registers) (digits : List Bool) (amount : Nat) :
    ∃ trace : List (State C),Facts frame context memory digits amount trace := by
  obtain ⟨path⟩ := actual (.halt : Statement C) frame context memory digits amount
  have frames : ∀ slot,¬Work slot → (entry frame context memory digits amount).stk slot = frame slot :=
    cells_frame frame digits (unary amount) []
  have resources := trace_resources path.trace (entry frame context memory digits amount) frame
    (mass frame context memory digits amount) path.first path.chain
    (RatInput.Encoder.point_mass _) frames
  have grow : mass frame context memory digits amount+2*path.trace.length ≤
      scale frame context memory digits amount := Nat.add_le_add_left (Nat.mul_le_mul_left 2 path.count) _
  have perSlot : ∀ current ∈ path.trace,∀ slot,(current.stk slot).length ≤
      scale frame context memory digits amount :=
    fun current member slot => ((resources current member).2.1 slot).trans grow
  refine ⟨path.trace,{
    first := path.first,chain := path.chain,last := path.last,count := path.count,
    boundaries := ?_,proper := ?_ }⟩
  · intro current member
    exact ⟨(resources current member).1,perSlot current member,
      RatInput.Encoder.occupied_bound current.stk _ (perSlot current member),(resources current member).2.2⟩
  · have proper := NativeMulLink.no_early_halt_port (program (C:=C) .halt) .done rfl
      path.trace (final frame context digits amount) path.chain path.last rfl
    intro current member
    refine ⟨proper current member,?_⟩
    intro point selected
    have old := resources current (List.mem_of_mem_dropLast member)
    have cap := internal_resources current point _ (perSlot current (List.mem_of_mem_dropLast member))
    refine ⟨?_,cap.2⟩
    intro node present
    have fields := cap.1 node present
    exact ⟨fields.1.trans old.1,RatInput.Encoder.occupied_bound node.2 _ fields.2.1,
      fun slot untouched => (fields.2.2 slot untouched).trans (old.2.2 slot untouched)⟩

theorem charge_le (frame : Bank) (context : C) (memory : Registers) (digits : List Bool) (amount : Nat)
    (trace : List (State C)) (facts : Facts frame context memory digits amount trace) :
    charge trace ≤ time digits amount*(6*(scale frame context memory digits amount+3)+1) := by
  have bounded : ∀ current ∈ trace.dropLast,(match current.l with
      | none => 0
      | some point => ScannerStatement.clock (program .halt point) current.var current.stk) ≤
        6*(scale frame context memory digits amount+3) := by
    intro current member
    cases selected : current.l with
    | none => exact Nat.zero_le _
    | some point => exact (facts.proper current member).2 point selected |>.2
  have sum := RatLeaf.map_sum_bound
    (fun current : State C => match current.l with
      | none => 0
      | some point => ScannerStatement.clock (program .halt point) current.var current.stk)
    trace.dropLast (6*(scale frame context memory digits amount+3)) bounded
  have size : trace.dropLast.length ≤ trace.length := by simp only [List.length_dropLast]; omega
  have count := facts.count
  dsimp [charge]
  nlinarith

end RootL01.SymbolicSource.Unary
