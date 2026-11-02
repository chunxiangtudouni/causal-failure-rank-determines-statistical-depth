module

public import PSTR_WordBool_RatPair_Run_001

/-! The whole fixed program's exact write set and constant syntax bounds.
No dynamic field value, length, or answer appears in these code bounds. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Link

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

def Work (slot : Stack) : Prop := RatInput.Encoder.Work slot ∨ slot=8 ∨ slot=9

instance (slot : Stack) : Decidable (Work slot) := by unfold Work;infer_instance

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

theorem program_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point)≤32 := by
  cases point with
  | collect point => fin_cases point <;> exact of_decide_eq_true rfl
  | serialize point =>
    cases point with
    | boot which => cases which <;> exact of_decide_eq_true rfl
    | phase which old =>
      cases which <;> cases old <;> first
      | exact of_decide_eq_true rfl
      | (rename_i small;fin_cases small <;> exact of_decide_eq_true rfl)
    | trim which => cases which <;> exact of_decide_eq_true rfl
    | done => exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point)≤32 := by
  cases point with
  | collect point => fin_cases point <;> exact of_decide_eq_true rfl
  | serialize point =>
    cases point with
    | boot which => cases which <;> exact of_decide_eq_true rfl
    | phase which old =>
      cases which <;> cases old <;> first
      | exact of_decide_eq_true rfl
      | (rename_i small;fin_cases small <;> exact of_decide_eq_true rfl)
    | trim which => cases which <;> exact of_decide_eq_true rfl
    | done => exact of_decide_eq_true rfl

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C:=C) .halt point) := by
  cases point with
  | collect point => fin_cases point <;> exact of_decide_eq_true rfl
  | serialize point =>
    cases point with
    | boot which => cases which <;> exact of_decide_eq_true rfl
    | phase which old =>
      cases which <;> cases old <;> first
      | exact of_decide_eq_true rfl
      | (rename_i small;fin_cases small <;> exact of_decide_eq_true rfl)
    | trim which => cases which <;> exact of_decide_eq_true rfl
    | done => exact of_decide_eq_true rfl

theorem program_proper (caller : Statement C) (point : Label) (proper : point≠done) :
    program caller point=program .halt point := by
  cases point with
  | collect point => rfl
  | serialize point =>
    by_cases same : point=.done
    · subst point
      exact False.elim (proper rfl)
    · simp only [program,same,ite_false]

theorem caller_port (caller : Statement C) : program caller done=caller := rfl

def outside (background : Stack → List Bool) : Nat :=
  ∑ slot,if Work slot then 0 else (background slot).length

theorem initial_frame (background : Stack → List Bool) (source scratch : List Bool)
    (slot : Stack) (untouched : ¬Work slot) : initial background source scratch slot=background slot := by
  fin_cases slot <;> first | rfl | exact False.elim (untouched (by decide))

theorem occupied_initial (background : Stack → List Bool) (source scratch : List Bool) :
    RatInput.occupied (initial background source scratch)=outside background+source.length+scratch.length := by
  simp [RatInput.occupied,initial,clean,Collector.bank,Serializer.bank,outside,Work,RatInput.Encoder.Work,
    Fin.sum_univ_succ,Nat.add_assoc]
  omega

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Link
