module

public import PSTR_WordBool_WordOutput_Run_001

/-! Fixed syntax and owned stack writes of this one final serializer. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.WordOutput

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

abbrev Work := RatInput.Encoder.Work

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
  | collect point | suffix point =>
    cases point <;> first
    | exact of_decide_eq_true rfl
    | (rename_i small;fin_cases small <;> exact of_decide_eq_true rfl)
  | prepare => exact of_decide_eq_true rfl
  | trim => exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point)≤32 := by
  cases point with
  | collect point | suffix point =>
    cases point <;> first
    | exact of_decide_eq_true rfl
    | (rename_i small;fin_cases small <;> exact of_decide_eq_true rfl)
  | prepare => exact of_decide_eq_true rfl
  | trim => exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C:=C) .halt point) := by
  cases point with
  | collect point | suffix point =>
    cases point <;> first
    | exact of_decide_eq_true rfl
    | (rename_i small;fin_cases small <;> exact of_decide_eq_true rfl)
  | prepare => exact of_decide_eq_true rfl
  | trim => exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem program_proper (caller : Statement C) (point : Label) (proper : point≠.done) :
    program caller point=program .halt point := by
  cases point <;> first | rfl | exact False.elim (proper rfl)

def fieldSize (r : Rat) : Nat := RatInput.Encoder.fieldSize r
def space (background : Stack → List Bool) (r : Rat) (tail scratch : List Bool) : Nat :=
  RatInput.Encoder.outside background+tail.length+scratch.length+258*fieldSize r+1286

def entry (background : Stack → List Bool) (context : C) (hit map : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (r : Rat) (tail scratch : List Bool) : State C :=
  ⟨some (.collect (.collect 0)),(((context,hit,map),memory),formatter),
    RatInput.Encoder.bank background (RatInput.Encoder.packet r tail) scratch [] [] [] [] [] [] []⟩

theorem boolTail_length (hit map : Bool) : (boolTail hit map).length=9 := by cases hit <;> cases map <;> decide

end PaperProofs.Common.Native.PSTRWordBool.WordOutput
