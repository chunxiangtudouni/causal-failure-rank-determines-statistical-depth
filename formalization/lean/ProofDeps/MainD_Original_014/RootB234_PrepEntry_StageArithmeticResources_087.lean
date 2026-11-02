module

public import RootB234_PrepEntry_StageArithmeticSyntax_086

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageArithmetic
open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM RootB234.PrepExponent RootL01.SymbolicSource
open B23_4_RatWordPrep
variable {C : Type*}
variable {multiply : Bool}

def Protected (slot : Stack) : Prop := slot=1 ∨ slot=8 ∨ slot=9 ∨ slot=11
def Work (slot : Stack) : Prop := ¬Protected slot
instance (slot : Stack) : Decidable (Protected slot) := by unfold Protected;infer_instance
instance (slot : Stack) : Decidable (Work slot) := by unfold Work;infer_instance

private theorem writes_store {σ τ Λ : Type*} (iso : σ≃τ) (allowed : Stack→Prop)
    (body : TM2.Stmt RatInput.Alphabet Λ σ) :
    StackIso.WritesOnly allowed (StoreIso.statement iso body)↔StackIso.WritesOnly allowed body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih => exact and_congr Iff.rfl ih
  | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact and_congr yes no
  | goto _ | halt => rfl

private theorem writes_mono {σ Λ : Type*} (old new : Stack→Prop) (body : TM2.Stmt RatInput.Alphabet Λ σ)
    (included : ∀ slot,old slot→new slot) (written : StackIso.WritesOnly old body) : StackIso.WritesOnly new body := by
  induction body with
  | push slot _ _ ih | pop slot _ _ ih => exact ⟨included slot written.1,ih written.2⟩
  | peek _ _ _ ih | load _ _ ih => exact ih written
  | branch _ _ _ yes no => exact ⟨yes written.1,no written.2⟩
  | goto _ | halt => trivial

private theorem writes_stack {σ Λ : Type*} (roles : Stack≃Stack) (allowed : Stack→Prop)
    (body : TM2.Stmt RatInput.Alphabet Λ σ) (written : StackIso.WritesOnly allowed body) :
    StackIso.WritesOnly (fun slot => allowed (roles.symm slot)) (StackIso.statement roles body) := by
  induction body with
  | push slot _ _ ih | pop slot _ _ ih => exact ⟨by simpa only [Equiv.symm_apply_apply] using written.1,ih written.2⟩
  | peek _ _ _ ih | load _ _ ih => exact ih written
  | branch _ _ _ yes no => exact ⟨yes written.1,no written.2⟩
  | goto _ | halt => trivial

theorem program_writes (multiply : Bool) (point : Label) : StackIso.WritesOnly Work (program multiply (C:=C) .halt point) := by
  cases point with
  | stash point | restore point =>
    rw [program,StackIso.writes_labelMap]
    apply writes_mono StageStash.Work Work _ _ (StageStash.source_writes point)
    intro slot owned
    fin_cases slot <;> first | exact of_decide_eq_true rfl | exact False.elim (by simp [StageStash.Work,StageStash.index] at owned)
  | binary point =>
    rw [program,StackIso.writes_labelMap,binary,writes_store]
    cases multiply
    all_goals simp only [Bool.false_eq_true,ite_false,ite_true]
    all_goals change StackIso.WritesOnly Work (StoreIso.statement _ (StackIso.statement Arithmetic.binaryRoles (RatBinary.program _ .halt point)))
    all_goals rw [writes_store]
    all_goals apply writes_mono Arithmetic.Work Work _ _ (writes_stack Arithmetic.binaryRoles RatPair.Link.Work _ (RatBinary.program_writes _ point))
    all_goals intro slot owned untouched
    all_goals exact (Arithmetic.frame_roles slot (by rcases untouched with rfl|rfl|rfl|rfl <;> simp)) owned
  | done => trivial

theorem step_context (before after : State C) (edge : TM2.step (program multiply .halt) before=some after) :
    QLoop.rootContext after.var=QLoop.rootContext before.var := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program multiply .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact RawGetter.nodes_readonly QLoop.rootContext _ (program_readonly multiply point) memory contents _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (trace : List (State C)) (before : State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program multiply .halt) a=some b)) :
    ∀ current∈trace,QLoop.rootContext current.var=QLoop.rootContext before.var := by
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
    (edge : TM2.step (program multiply .halt) before=some after)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    (∀ slot,(after.stk slot).length≤bound+32) ∧
      ∀ slot,¬Work slot→after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program multiply .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact ⟨fun slot => (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
        (Nat.add_le_add_left (program_pushes multiply point) bound),
        fun slot untouched => StackIso.nodes_frame _ _ (program_writes multiply point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)⟩

theorem trace_resources (trace : List (State C)) (before : State C) (background : RatInput.Stack → List Bool)
    (bound : Nat) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program multiply .halt) a=some b))
    (bounded : ∀ slot,(before.stk slot).length≤bound)
    (frame : ∀ slot,¬Work slot→before.stk slot=background slot) :
    ∀ current∈trace,(∀ slot,(current.stk slot).length≤bound+32*trace.length) ∧
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
      · have tail := ih next (bound+32) rfl tailChain step.1
          (fun slot untouched => (step.2 slot untouched).trans (frame slot untouched)) current later
        refine ⟨?_,tail.2⟩
        intro slot
        have h := tail.1 slot
        simp only [List.length_cons] at h ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length≤bound) :
    (∀ node∈AuxWorkspace.nodes (program multiply .halt point) current.var current.stk,
      QLoop.rootContext node.1=QLoop.rootContext current.var ∧ (∀ slot,(node.2 slot).length≤bound+32) ∧
        ∀ slot,¬Work slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (program multiply .halt point) current.var current.stk≤64*(bound+33) := by
  refine ⟨?_,?_⟩
  · intro node member
    exact ⟨RawGetter.nodes_readonly QLoop.rootContext _ (program_readonly multiply point) current.var current.stk node member,
      fun slot => (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes multiply point) bound),
      fun slot untouched => StackIso.nodes_frame _ _ (program_writes multiply point) current.var current.stk slot untouched node member⟩
  · exact (ScannerClock.clock_bound (program multiply .halt point) current.var current.stk bound bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions multiply point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes multiply point) bound) 1))



def coefficient : Nat := 16*(33+32*timeCoefficient)+64*(34+32*timeCoefficient)+timeCoefficient

theorem resource_envelope (occupied : Nat) :
    timeCoefficient*(occupied+1)^4≤coefficient*(occupied+1)^4 ∧
    16*(occupied+32*(timeCoefficient*(occupied+1)^4))≤coefficient*(occupied+1)^4 ∧
    16*(occupied+32*(timeCoefficient*(occupied+1)^4)+32)≤coefficient*(occupied+1)^4 ∧
    64*(occupied+32*(timeCoefficient*(occupied+1)^4)+33)≤coefficient*(occupied+1)^4 := by
  have base : 1≤occupied+1 := by omega
  have power : occupied+1≤(occupied+1)^4 := by simpa only [pow_one] using Nat.pow_le_pow_right base (by decide : 1≤4)
  have one : 1≤(occupied+1)^4 := base.trans power
  unfold coefficient
  constructor
  · have small : timeCoefficient≤16*(33+32*timeCoefficient)+64*(34+32*timeCoefficient)+timeCoefficient := by omega
    exact Nat.mul_le_mul_right _ small
  constructor
  · nlinarith only [power,one,Nat.zero_le (timeCoefficient*(occupied+1)^4)]
  constructor
  · nlinarith only [power,one,Nat.zero_le (timeCoefficient*(occupied+1)^4)]
  · nlinarith only [power,one,Nat.zero_le (timeCoefficient*(occupied+1)^4)]

end RootB234.PrepEntry.StageArithmetic
