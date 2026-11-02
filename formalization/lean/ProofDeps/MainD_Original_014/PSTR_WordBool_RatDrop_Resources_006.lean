module

public import PSTR_WordBool_RatDrop_Run_005

/-! All actual internal nodes of the fixed packet consumer are bounded
from the current data mass; only physical3 and15 may be written. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatDrop

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

theorem program_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point)≤4 := by
  fin_cases point <;> exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point)≤2 := by
  fin_cases point <;> exact of_decide_eq_true rfl

theorem program_writes (point : Label) :
    StackIso.WritesOnly (fun slot : Stack=>slot=15 ∨ slot=3) (program (C:=C) .halt point) := by
  fin_cases point <;> simp [program,headerBody,fieldBody,put,LabelMap.statement,StackIso.statement,
    RatOutput.program,RatOutput.jump,reverseRoles,Equiv.swap_apply_def,StackIso.WritesOnly]

theorem internal_bound (background : Stack→List Bool) (context : C) (current : State C) (bound : Nat)
    (safe : Safe background context bound current) (point : Label) :
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      (∀ slot,(node.2 slot).length≤bound+2) ∧
      ∀ slot,slot≠15→slot≠3→node.2 slot=background slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk≤8*(bound+3) := by
  have bounded : ∀ slot,(current.stk slot).length≤bound:=fun slot=>(RatInput.Encoder.point_mass current.stk slot).trans safe.2.2
  refine ⟨?_,?_⟩
  · intro node member
    refine ⟨?_,?_⟩
    · intro slot
      exact (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes point) bound)
    · intro slot notSource notPark
      have unchanged:=StackIso.nodes_frame _ _ (program_writes point) current.var current.stk slot
        (by simp only [notSource,notPark,or_self,not_false_eq_true]) node member
      exact unchanged.trans (safe.2.1 slot notSource notPark)
  · exact (ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))

end PaperProofs.Common.Native.PSTRWordBool.RatDrop
