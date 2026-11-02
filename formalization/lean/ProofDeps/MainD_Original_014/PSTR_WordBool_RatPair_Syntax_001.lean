module

public import PSTR_WordBool_RatPair_Collect_001

/-! Fixed collector syntax. Only the six owned bank cells can change;
unread0/archive1 and every other cell are protected at internal nodes. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Collector

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

def Work (slot : Stack) : Prop := slot=3 ∨ slot=4 ∨ slot=7 ∨ slot=8 ∨ slot=9 ∨ slot=15

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

theorem program_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point)≤15 := by
  fin_cases point <;> exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point)≤15 := by
  fin_cases point <;> exact of_decide_eq_true rfl

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C:=C) .halt point) := by
  fin_cases point <;> exact of_decide_eq_true rfl

theorem program_proper (caller : Statement C) (point : Label) (proper : point≠7) :
    program caller point=program .halt point := by
  fin_cases point <;> first | rfl | exact False.elim (proper rfl)

theorem bank_frame (background : Stack → List Bool) (source scratch xn xd yn yd : List Bool)
    (slot : Stack) (untouched : ¬Work slot) :
    bank background source scratch xn xd yn yd slot=background slot := by
  simp only [Work,not_or] at untouched
  rcases untouched with ⟨n3,n4,n7,n8,n9,n15⟩
  simp only [bank,n3,n4,n7,n8,n9,n15,ite_false]

def outside (background : Stack → List Bool) : Nat :=
  ∑ slot,if Work slot then 0 else (background slot).length

theorem occupied_bank (background : Stack → List Bool) (source scratch xn xd yn yd : List Bool) :
    RatInput.occupied (bank background source scratch xn xd yn yd)=
      outside background+source.length+scratch.length+xn.length+xd.length+yn.length+yd.length := by
  simp [RatInput.occupied,bank,outside,Work,Fin.sum_univ_succ,Nat.add_assoc]
  omega

theorem packets_length (sx sy : Bool) (xn xd yn yd tail : List Bool) :
    (packets sx sy xn xd yn yd tail).length=2*fieldSize xn xd yn yd+12+tail.length := by
  simp only [packets,PSTRSymbolicRatExport.packet,List.length_cons,List.length_append,RatOutput.flagged_length,fieldSize]
  omega

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Collector
