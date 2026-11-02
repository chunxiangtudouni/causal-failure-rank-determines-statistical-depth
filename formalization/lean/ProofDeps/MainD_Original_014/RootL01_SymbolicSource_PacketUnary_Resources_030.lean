module
public import RootL01_SymbolicSource_PacketUnary_Run_029

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootL01.SymbolicSource.PacketUnary
open Turing
open PaperProofs.Common.Native
open PSTRWordVM PSTRWordBool RationalControllerComputation
variable {C : Type*}

def Work (slot : RatInput.Stack) : Prop := slot=3 ∨ slot=5 ∨ slot=6 ∨ slot=7 ∨ slot=15
instance (slot : RatInput.Stack) : Decidable (Work slot) := by unfold Work;infer_instance
def writesDecidable : (body : Statement C) → Decidable (StackIso.WritesOnly Work body)
  | .push slot _ tail | .pop slot _ tail => by
    change Decidable (Work slot ∧ StackIso.WritesOnly Work tail)
    letI:=writesDecidable tail
    infer_instance
  | .peek _ _ tail | .load _ tail => writesDecidable tail
  | .branch _ yes no => by
    change Decidable (StackIso.WritesOnly Work yes ∧ StackIso.WritesOnly Work no)
    letI:=writesDecidable yes
    letI:=writesDecidable no
    infer_instance
  | .goto _ | .halt => isTrue trivial
local instance (body : Statement C) : Decidable (StackIso.WritesOnly Work body) := writesDecidable body

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C:=C) .halt point) := by
  cases point with
  | collect point => fin_cases point <;> exact of_decide_eq_true rfl
  | convert point => cases point <;> exact of_decide_eq_true rfl
  | done => trivial

theorem program_readonly (point : Label) :
    RatLeaf.Readonly (fun memory : Store C => memory.1.1) (program .halt point) := by
  cases point with
  | collect point =>
    fin_cases point
    all_goals
      dsimp [program,RatLeaf.Readonly,L01_3_5_TABLE_NatSerializer019.collectProgram,
        LabelMap.statement,RatInput.program,RatInput.fieldBody,RatInput.restoreBody,
        StackIso.statement,PSTRSymbolicNaturalExport.program,PSTRSymbolicRatExport.restoreLabel]
      repeat' constructor
      all_goals (intros; rfl)
  | convert point =>
    cases point <;>
      dsimp [program,LabelMap.statement,StoreIso.statement,convertIso,Unary.program,
        Unary.baseProgram,ContextLift.statement,RatLeaf.Readonly,Unary.captureBit,Unary.capturePresent]
    all_goals repeat' constructor
    all_goals (intros; rfl)
  | done => trivial

theorem entryBank_frame (frame : Bank) (value : Nat) (tail : List Bool) (slot : RatInput.Stack)
    (untouched : ¬Work slot) : entryBank frame value tail slot=frame slot := by
  have a : slot ≠ 15 := fun equal => untouched (Or.inr (Or.inr (Or.inr (Or.inr equal))))
  have b : ¬(slot=3 ∨ slot=5 ∨ slot=6) := by
    intro selected
    rcases selected with eq | eq | eq
    · exact untouched (Or.inl eq)
    · exact untouched (Or.inr (Or.inl eq))
    · exact untouched (Or.inr (Or.inr (Or.inl eq)))
  simp only [entryBank,a,b,ite_false]

theorem step_context (before after : State C) (edge : TM2.step (program .halt) before = some after) :
    after.var.1.1 = before.var.1.1 := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after = TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact RatLeaf.nodes_readonly (fun value : Store C => value.1.1) _ (program_readonly point)
        memory contents _ (AuxWorkspace.endpoint_mem _ _ _)

theorem step_resources (before after : State C) (bound : Nat)
    (edge : TM2.step (program .halt) before = some after)
    (bounded : ∀ slot,(before.stk slot).length ≤ bound) :
    (∀ slot,(after.stk slot).length ≤ bound+7) ∧
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
          (Nat.add_le_add_left (program_pushes point) bound)
      · intro slot untouched
        exact StackIso.nodes_frame Work _ (program_writes point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_resources (trace : List (State C)) (before : State C) (frame : Bank) (bound : Nat)
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a = some b))
    (bounded : ∀ slot,(before.stk slot).length ≤ bound)
    (frames : ∀ slot,¬Work slot → before.stk slot = frame slot) :
    ∀ current ∈ trace,current.var.1.1 = before.var.1.1 ∧
      (∀ slot,(current.stk slot).length ≤ bound+7*trace.length) ∧
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
      · have tail := ih next (bound+7) rfl tailChain step.1 nextFrames current later
        refine ⟨tail.1.trans (step_context before next edge),?_,tail.2.2⟩
        intro slot
        have perSlot := tail.2.1 slot
        simp only [List.length_cons] at perSlot ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length ≤ bound) :
    (∀ node ∈ AuxWorkspace.nodes (program .halt point) current.var current.stk,
      node.1.1.1 = current.var.1.1 ∧ (∀ slot,(node.2 slot).length ≤ bound+7) ∧
      ∀ slot,¬Work slot → node.2 slot = current.stk slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk ≤ 18*(bound+8) := by
  refine ⟨?_,?_⟩
  · intro node member
    refine ⟨RatLeaf.nodes_readonly _ _ (program_readonly point) _ _ node member,?_,?_⟩
    · intro slot
      exact (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes point) bound)
    · intro slot untouched
      exact StackIso.nodes_frame Work _ (program_writes point) current.var current.stk slot untouched node member
  · have clock := ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded
    exact clock.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
      (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))

def mass (frame : Bank) (value : Nat) (tail : List Bool) : Nat :=
  RatInput.occupied (entryBank frame value tail)
def scale (frame : Bank) (value : Nat) (tail : List Bool) : Nat := mass frame value tail+7*time value
def statementClock (current : State C) : Nat := match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program .halt point) current.var current.stk
def charge (trace : List (State C)) : Nat := trace.length+(trace.dropLast.map statementClock).sum

structure Facts (frame : Bank) (context : C) (registers : Unary.Registers) (rat : RatInput.Store)
    (value : Nat) (tail : List Bool) (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (entry frame context registers rat value tail)
  chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b)
  last : trace.getLast?=some final
  active : final.l=some .done
  context_eq : final.var.1.1=context
  contents : final.stk=Function.update (entryBank frame value tail) 5 (Unary.unary value)
  count : trace.length ≤ time value
  boundaries : ∀ current ∈ trace,current.var.1.1=context ∧
    (∀ slot,(current.stk slot).length ≤ scale frame value tail) ∧
    RatInput.occupied current.stk ≤ 16*scale frame value tail ∧
    ∀ slot,¬Work slot → current.stk slot=frame slot
  proper : ∀ current ∈ trace.dropLast,current.l ≠ some .done ∧
    ∀ point,current.l=some point →
      (∀ node ∈ AuxWorkspace.nodes (program .halt point) current.var current.stk,
        node.1.1.1=context ∧ RatInput.occupied node.2 ≤ 16*(scale frame value tail+7) ∧
        ∀ slot,¬Work slot → node.2 slot=frame slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk ≤ 18*(scale frame value tail+8)

theorem actual_bounded (frame : Bank) (context : C) (registers : Unary.Registers) (rat : RatInput.Store)
    (value : Nat) (tail : List Bool) :
    ∃ (trace : List (State C)) (final : State C),Facts frame context registers rat value tail trace final := by
  obtain ⟨trace,final,first,chain,last,active,context_eq,contents,count⟩ :=
    actual .halt frame context registers rat value tail
  let before := entry frame context registers rat value tail
  have frames : ∀ slot,¬Work slot → before.stk slot=frame slot := entryBank_frame frame value tail
  have resources := trace_resources trace before frame (mass frame value tail) first chain
    (RatInput.Encoder.point_mass _) frames
  have grow : mass frame value tail+7*trace.length ≤ scale frame value tail :=
    Nat.add_le_add_left (Nat.mul_le_mul_left 7 count) _
  have perSlot : ∀ current ∈ trace,∀ slot,(current.stk slot).length ≤ scale frame value tail :=
    fun current present slot => ((resources current present).2.1 slot).trans grow
  refine ⟨trace,final,{
    first:=first,chain:=chain,last:=last,active:=active,context_eq:=context_eq,contents:=contents,count:=count,
    boundaries:=?_,proper:=?_ }⟩
  · intro current present
    exact ⟨(resources current present).1,perSlot current present,
      RatInput.Encoder.occupied_bound current.stk _ (perSlot current present),(resources current present).2.2⟩
  · have proper := NativeMulLink.no_early_halt_port (program (C:=C) .halt) .done rfl trace final chain last active
    intro current present
    refine ⟨proper current present,?_⟩
    intro point selected
    have old := resources current (List.mem_of_mem_dropLast present)
    have cap := internal_resources current point _ (perSlot current (List.mem_of_mem_dropLast present))
    refine ⟨?_,cap.2⟩
    intro node member
    have fields := cap.1 node member
    exact ⟨fields.1.trans old.1,RatInput.Encoder.occupied_bound node.2 _ fields.2.1,
      fun slot untouched => (fields.2.2 slot untouched).trans (old.2.2 slot untouched)⟩

theorem charge_le {frame : Bank} {context : C} {registers : Unary.Registers} {rat : RatInput.Store}
    {value : Nat} {tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts frame context registers rat value tail trace final) :
    charge trace ≤ time value*(18*(scale frame value tail+8)+1) := by
  have bounded : ∀ current ∈ trace.dropLast,statementClock current ≤ 18*(scale frame value tail+8) := by
    intro current member
    cases selected : current.l with
    | none => simp only [statementClock,selected]; exact Nat.zero_le _
    | some point =>
      have bound := (facts.proper current member).2 point selected |>.2
      simpa only [statementClock,selected] using bound
  have sum := RatLeaf.map_sum_bound statementClock trace.dropLast (18*(scale frame value tail+8)) bounded
  have size : trace.dropLast.length ≤ trace.length := by simp only [List.length_dropLast]; omega
  have count := facts.count
  dsimp [charge]
  nlinarith

end RootL01.SymbolicSource.PacketUnary
