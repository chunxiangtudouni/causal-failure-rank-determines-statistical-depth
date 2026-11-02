module

public import RootB234_PrepEntry_NatRun_001
public import B23_4_RatWordPrep_SeqCmp_StackFrame_047

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.Nat

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

abbrev Label := HeaderNat.Label
abbrev Store (C : Type*) := HeaderNat.Store C
abbrev Statement (C : Type*) := HeaderNat.Statement C
abbrev State (C : Type*) := HeaderNat.State C

variable {C : Type*}

def program (caller : Statement C) : Label → Statement C := HeaderNat.program caller

def entry (context : C) (bits : List Bool) : State C := HeaderNat.entry context default (fun _ => []) bits

def callerContext (memory : Store C) : C := memory.1.1

def Work (slot : RatInput.Stack) : Prop := slot=0 ∨ slot=1 ∨ slot=7 ∨ slot=8
instance (slot : RatInput.Stack) : Decidable (Work slot) := by unfold Work; infer_instance

theorem program_accesses (point : Label) : Frame.AccessesOnly Work (program (C := C) .halt point) := by
  cases point with
  | header point => fin_cases point <;> exact of_decide_eq_true rfl
  | field point => fin_cases point <;> exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem program_actions (point : Label) : ScannerClock.actions (program (C := C) .halt point) ≤ 16 := by
  cases point with
  | header point => fin_cases point <;> exact of_decide_eq_true rfl
  | field point => fin_cases point <;> exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C := C) .halt point) ≤ 16 := by
  cases point with
  | header point => fin_cases point <;> exact of_decide_eq_true rfl
  | field point => fin_cases point <;> exact of_decide_eq_true rfl
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
    dsimp [RawGetter.Readonly,program,callerContext,
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


end RootB234.PrepEntry.Nat
