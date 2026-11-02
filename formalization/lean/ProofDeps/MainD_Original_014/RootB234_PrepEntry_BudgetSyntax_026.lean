module

public import RootB234_PrepEntry_BudgetCode_025
public import B23_4_RatWordPrep_SeqCmp_StackFrame_047

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.Budget

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*}

def Work (slot : RatInput.Stack) : Prop := slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 ∨ slot=7 ∨ slot=8 ∨ slot=9 ∨ slot=15
instance (slot : RatInput.Stack) : Decidable (Work slot) := by unfold Work; infer_instance

theorem program_accesses (point : Label) : Frame.AccessesOnly Work (program (C := C) .halt point) := by
  cases point
  all_goals repeat' first
    | (rename_i point; fin_cases point)
    | (rename_i point; cases point)
  all_goals exact of_decide_eq_true rfl

theorem program_actions (point : Label) : ScannerClock.actions (program (C := C) .halt point) ≤ 16 := by
  cases point with
  | restore point =>
    rw [program,LabelMap.statement_actions]
    exact Restore.program_actions point
  | copy point =>
    rw [program,LabelMap.statement_actions,StoreIso.statement_actions]
    exact WholeCopy.program_actions point
  | raw point =>
    rw [program,LabelMap.statement_actions,StoreIso.statement_actions]
    exact (RawNative.program_actions point).trans (by decide)
  | budget point =>
    rw [program,LabelMap.statement_actions,StoreIso.statement_actions]
    exact (RootB234.PrepBudgetArchive.fixed_actions point).trans (by decide)
  | rewind point =>
    cases point with
    | clear second => fin_cases second <;> exact of_decide_eq_true rfl
    | move | done => exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C := C) .halt point) ≤ 16 := by
  cases point with
  | restore point =>
    rw [program,LabelMap.statement_pushes]
    exact Restore.program_pushes point
  | copy point =>
    rw [program,LabelMap.statement_pushes,StoreIso.statement_pushes]
    exact WholeCopy.program_pushes point
  | raw point =>
    rw [program,LabelMap.statement_pushes,StoreIso.statement_pushes]
    exact (RawNative.program_pushes point).trans (by decide)
  | budget point =>
    rw [program,LabelMap.statement_pushes,StoreIso.statement_pushes]
    exact (RootB234.PrepBudgetArchive.fixed_pushes point).trans (by decide)
  | rewind point =>
    cases point with
    | clear second => fin_cases second <;> exact of_decide_eq_true rfl
    | move | done => exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

private theorem accesses_writes (body : Statement C) (good : Frame.AccessesOnly Work body) :
    StackIso.WritesOnly Work body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih => exact ⟨good.1,ih good.2⟩
  | peek _ _ _ ih => exact ih good.2
  | load _ _ ih => exact ih good
  | branch _ _ _ yes no => exact ⟨yes good.1,no good.2⟩
  | goto _ | halt => trivial

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C := C) .halt point) :=
  accesses_writes _ (program_accesses point)


theorem entry_slots (context : C) (bits : List Bool) :
    (entry context bits).stk=(fun slot => if slot=0 then bits else []) := by
  funext slot
  fin_cases slot <;> rfl

theorem entry_mass (context : C) (bits : List Bool) : RatInput.occupied (entry context bits).stk=bits.length := by
  rw [entry_slots]
  simp [RatInput.occupied,Fin.sum_univ_succ]

theorem initial_default {C : Type*} [Inhabited C] (bits : List Bool) :
    entry (default : C) bits=TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store C) 0 bits := by
  change (⟨some (default : Label),(default : Store C),_⟩ : State C)=⟨some default,default,_⟩
  congr 1
  funext slot
  fin_cases slot <;> rfl

private theorem supports_stmt (body : Statement C) :
    TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C := C) .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

theorem program_readonly (point : Label) : RawGetter.Readonly (callerContext (C := C)) (program .halt point) := by
  cases point
  all_goals repeat' first
    | (rename_i point; fin_cases point)
    | (rename_i point; cases point)
  all_goals
    dsimp [RawGetter.Readonly,program,callerContext,rawIso,budgetIso,Restore.copyIso,
      Restore.program,RawNative.program,RawNative.source,
      RootB234.PrepBudgetArchive.program,RootB234.PrepBudgetArchive.captureBit,
      RootB234.PrepBudgetArchive.captureFlag,RootB234.PrepBudgetArchive.remember,
      WholeCopy.program,WholeCopy.capture,WholeCopy.present,WholeCopy.bit,
      NJ.program,NJ.alphaIso,Alpha.program,Alpha.source,Rewind.program,Rewind.clearSlot,
      HeaderNat.program,HeaderNat.fieldIso,Header.program,Header.source,NatField.program,
      PSTRSymbolicRatExport.fieldBody,PSTRSymbolicNaturalExport.program,
      LabelMap.statement,StoreIso.statement,StoreIso.machine,StoreIso.exchange,StackIso.statement,
      VirtualReturn.program,VirtualReturn.statement,VirtualReturn.core,VirtualBool.source,BoolOnStacks.program,ContextLift.statement]
    repeat' constructor
    all_goals (intros; rfl)

theorem step_context (before after : State C) (edge : TM2.step (program .halt) before=some after) :
    callerContext after.var=callerContext before.var := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact RawGetter.nodes_readonly callerContext _ (program_readonly point) memory contents _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (trace : List (State C)) (before : State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b)) :
    ∀ current∈trace,callerContext current.var=callerContext before.var := by
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
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    (∀ slot,(after.stk slot).length≤bound+16) ∧
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
    (bounded : ∀ slot,(before.stk slot).length≤bound)
    (frame : ∀ slot,¬Work slot→before.stk slot=background slot) :
    ∀ current∈trace,(∀ slot,(current.stk slot).length≤bound+16*trace.length) ∧
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
      · have tail := ih next (bound+16) rfl tailChain step.1
          (fun slot untouched => (step.2 slot untouched).trans (frame slot untouched)) current later
        refine ⟨?_,tail.2⟩
        intro slot
        have h := tail.1 slot
        simp only [List.length_cons] at h ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length≤bound) :
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      callerContext node.1=callerContext current.var ∧ (∀ slot,(node.2 slot).length≤bound+16) ∧
        ∀ slot,¬Work slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk≤32*(bound+17) := by
  refine ⟨?_,?_⟩
  · intro node member
    exact ⟨RawGetter.nodes_readonly callerContext _ (program_readonly point) current.var current.stk node member,
      fun slot => (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes point) bound),
      fun slot untouched => StackIso.nodes_frame _ _ (program_writes point) current.var current.stk slot untouched node member⟩
  · exact (ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))


end RootB234.PrepEntry.Budget
