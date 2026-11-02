module

public import B23_4_RatWordPrep_SeqCmp_OriginalPreludeCode_057

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.OriginalPrelude

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

variable {C : Type*}

def Work (slot : RatInput.Stack) : Prop := OriginalFee.Work slot ∨ slot=2 ∨ slot=3 ∨ slot=8
instance (slot : RatInput.Stack) : Decidable (Work slot) := by unfold Work; infer_instance

theorem program_accesses (point : Label) : Frame.AccessesOnly Work (program (C := C) .halt point) := by
  cases point with
  | copy point => cases point <;> exact of_decide_eq_true rfl
  | header point =>
    cases point with
    | header point => fin_cases point <;> exact of_decide_eq_true rfl
    | field point => fin_cases point <;> exact of_decide_eq_true rfl
    | done => exact of_decide_eq_true rfl
  | rewind point =>
    cases point with
    | clear second => fin_cases second <;> exact of_decide_eq_true rfl
    | move | done => exact of_decide_eq_true rfl
  | fee point =>
    cases point with
      | front point =>
        cases point with
        | front point =>
          cases point with
          | prior point => fin_cases point <;> exact of_decide_eq_true rfl
          | encoder point =>
            cases point with
            | collect point | num point | den point => fin_cases point <;> exact of_decide_eq_true rfl
            | reverseNum | reverseDen | finish | done => exact of_decide_eq_true rfl
          | done => exact of_decide_eq_true rfl
        | native point => fin_cases point <;> exact of_decide_eq_true rfl
        | done => exact of_decide_eq_true rfl
      | read point =>
        cases point with
        | boot | done => exact of_decide_eq_true rfl
        | parse point | extract point => fin_cases point <;> exact of_decide_eq_true rfl
      | done => exact of_decide_eq_true rfl
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

theorem program_actions (point : Label) : ScannerClock.actions (program (C := C) .halt point) ≤ 16 := by
  cases point with
  | copy point =>
    rw [program,LabelMap.statement_actions,StoreIso.statement_actions]
    exact WholeCopy.program_actions point
  | header point =>
    cases point with
    | header point => fin_cases point <;> exact of_decide_eq_true rfl
    | field point => fin_cases point <;> exact of_decide_eq_true rfl
    | done => exact of_decide_eq_true rfl
  | rewind point =>
    cases point with
    | clear second => fin_cases second <;> exact of_decide_eq_true rfl
    | move | done => exact of_decide_eq_true rfl
  | fee point =>
    rw [program,LabelMap.statement_actions,StoreIso.statement_actions,ContextLift.statement_actions]
    exact OriginalFee.program_actions point
  | done => exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C := C) .halt point) ≤ 16 := by
  cases point with
  | copy point =>
    rw [program,LabelMap.statement_pushes,StoreIso.statement_pushes]
    exact WholeCopy.program_pushes point
  | header point =>
    cases point with
    | header point => fin_cases point <;> exact of_decide_eq_true rfl
    | field point => fin_cases point <;> exact of_decide_eq_true rfl
    | done => exact of_decide_eq_true rfl
  | rewind point =>
    cases point with
    | clear second => fin_cases second <;> exact of_decide_eq_true rfl
    | move | done => exact of_decide_eq_true rfl
  | fee point =>
    rw [program,LabelMap.statement_pushes,StoreIso.statement_pushes,ContextLift.statement_pushes]
    exact OriginalFee.program_pushes point
  | done => exact of_decide_eq_true rfl

theorem entry_slots (context : C) (bits : List Bool) :
    (entry context bits).stk=(fun slot => if slot=0 then bits else []) := rfl

theorem entry_mass (context : C) (bits : List Bool) : RatInput.occupied (entry context bits).stk=bits.length := by
  rw [entry_slots]
  simp [RatInput.occupied,Fin.sum_univ_succ]

end B23_4_RatWordPrep.OriginalPrelude
