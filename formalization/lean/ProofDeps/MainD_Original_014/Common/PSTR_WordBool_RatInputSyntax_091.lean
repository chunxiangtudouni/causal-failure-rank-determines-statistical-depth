module

public import Common.PSTR_WordBool_RatInputRun_090

/-! Fixed source syntax and exact protected-stack writes for the encoder.
The constants do not depend on the encoded value or any loop count. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

def Work (slot : RatInput.Stack) : Prop :=
  slot=3 ∨ slot=4 ∨ slot=5 ∨ slot=6 ∨ slot=7 ∨ slot=12 ∨ slot=13 ∨ slot=14 ∨ slot=15

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

theorem program_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point)≤15 := by
  cases point with
  | collect point => fin_cases point <;> exact of_decide_eq_true rfl
  | reverseNum => exact of_decide_eq_true rfl
  | reverseDen => exact of_decide_eq_true rfl
  | den point => fin_cases point <;> exact of_decide_eq_true rfl
  | num point => fin_cases point <;> exact of_decide_eq_true rfl
  | finish => exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point)≤15 := by
  cases point with
  | collect point => fin_cases point <;> exact of_decide_eq_true rfl
  | reverseNum => exact of_decide_eq_true rfl
  | reverseDen => exact of_decide_eq_true rfl
  | den point => fin_cases point <;> exact of_decide_eq_true rfl
  | num point => fin_cases point <;> exact of_decide_eq_true rfl
  | finish => exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C:=C) .halt point) := by
  cases point with
  | collect point => fin_cases point <;> exact of_decide_eq_true rfl
  | reverseNum => exact of_decide_eq_true rfl
  | reverseDen => exact of_decide_eq_true rfl
  | den point => fin_cases point <;> exact of_decide_eq_true rfl
  | num point => fin_cases point <;> exact of_decide_eq_true rfl
  | finish => exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

end PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder

