module

public import B23_4_RatWordPrep_SeqCmp_OriginalFeeCode_030

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.OriginalFee

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

variable {C : Type*}

def Work (slot : RatInput.Stack) : Prop := RawGetter.Work slot ∨ RatInput.Encoder.Work slot
instance (slot : RatInput.Stack) : Decidable (Work slot) := by unfold Work; infer_instance

def writesDecidable : (body : Statement C) → Decidable (StackIso.WritesOnly Work body)
  | .push slot _ tail | .pop slot _ tail => by
    change Decidable (Work slot ∧ StackIso.WritesOnly Work tail)
    letI := writesDecidable tail
    infer_instance
  | .peek _ _ tail | .load _ tail => writesDecidable tail
  | .branch _ yes no => by
    change Decidable (StackIso.WritesOnly Work yes ∧ StackIso.WritesOnly Work no)
    letI := writesDecidable yes
    letI := writesDecidable no
    infer_instance
  | .goto _ | .halt => isTrue trivial

local instance (body : Statement C) : Decidable (StackIso.WritesOnly Work body) := writesDecidable body

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C := C) .halt point) := by
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

theorem program_actions (point : Label) : ScannerClock.actions (program (C := C) .halt point)≤16 := by
  cases point with
  | front point =>
    rw [program,LabelMap.statement_actions]
    exact (RatInput.Complement.program_actions point).trans (by decide)
  | read point =>
    rw [program,LabelMap.statement_actions,StoreIso.statement_actions]
    exact RawGetter.program_actions point
  | done => exact Nat.zero_le _

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C := C) .halt point)≤16 := by
  cases point with
  | front point =>
    rw [program,LabelMap.statement_pushes]
    exact (RatInput.Complement.program_pushes point).trans (by decide)
  | read point =>
    rw [program,LabelMap.statement_pushes,StoreIso.statement_pushes]
    exact RawGetter.program_pushes point
  | done => exact Nat.zero_le _

theorem entry_slots (memory : RawGetter.Store C) (native : RatInput.Complement.CalleeFlags)
    (reader : RatInput.Complement.Reader) (bits : List Bool) :
    (entry memory native reader bits).stk=(fun slot => if slot=0 then bits else []) := by
  funext slot
  fin_cases slot <;> rfl

theorem entry_mass (memory : RawGetter.Store C) (native : RatInput.Complement.CalleeFlags)
    (reader : RatInput.Complement.Reader) (bits : List Bool) :
    RatInput.occupied (entry memory native reader bits).stk=bits.length := by
  rw [entry_slots]
  simp [RatInput.occupied,Fin.sum_univ_succ]

end B23_4_RatWordPrep.OriginalFee
