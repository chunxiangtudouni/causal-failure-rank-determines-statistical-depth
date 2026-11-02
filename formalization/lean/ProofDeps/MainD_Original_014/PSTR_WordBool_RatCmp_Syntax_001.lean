module

public import PSTR_WordBool_RatCmp_Call_001

/-! Constant syntax and protected-stack writes of the complete callee. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatCmp.Link

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

def Work (slot : Stack) : Prop := slot=3 ∨ slot=7 ∨ slot=13 ∨ slot=14 ∨ slot=15
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

theorem program_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point)≤8 := by
  cases point with
  | sub point => fin_cases point <;> exact of_decide_eq_true rfl
  | read point => fin_cases point <;> exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point)≤3 := by
  cases point with
  | sub point => fin_cases point <;> exact of_decide_eq_true rfl
  | read point => fin_cases point <;> exact of_decide_eq_true rfl

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C:=C) .halt point) := by
  cases point with
  | sub point => fin_cases point <;> exact of_decide_eq_true rfl
  | read point => fin_cases point <;> exact of_decide_eq_true rfl

theorem program_proper (caller : Statement C) (point : Label) (proper : point≠done) :
    program caller point=program .halt point := by
  cases point with
  | sub point => rfl
  | read point =>
    by_cases same : point=4
    · subst point
      exact False.elim (proper rfl)
    · simp only [program,same,ite_false]

theorem caller_port (caller : Statement C) : program caller done=caller := rfl

theorem entry_frame (context : C) (flags : Reader.Store) (readerMemory : RatOutput.Store)
    (nativeMemory : BoolOnStacks.Store states) (background : Stack → List Bool) (x y : Rat)
    (slot : Stack) (untouched : ¬Work slot) :
    (entry context flags readerMemory nativeMemory background x y).stk slot=background slot := by
  have not13 : slot≠13:=by intro same;subst slot;exact untouched (by decide)
  have not14 : slot≠14:=by intro same;subst slot;exact untouched (by decide)
  change IsolatedRat.cells background (encode [.rational x,.rational y]) [] slot=background slot
  simp only [IsolatedRat.cells,not13,not14,ite_false]

end PaperProofs.Common.Native.PSTRWordBool.RatCmp.Link
