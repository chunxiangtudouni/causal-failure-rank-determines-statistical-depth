module
public import RootB236_Controller_BestUpdate_Public006

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.RankMerge
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
abbrev Stack := BestUpdate.Stack
abbrev Label := BestUpdate.Label
abbrev Alphabet := BestUpdate.Alphabet
abbrev Store := BestUpdate.Store
abbrev Statement := BestUpdate.Statement
abbrev State := BestUpdate.State
variable {C : Type*}
def unary := RankCompare.unary
def entry : Label := 0
def increment : Label := 3
def second : Label := 4
def clearRank : Label := 7
def done : Label := 11
/-- Static source-role exchange; the actual two counters remain physically9 and2. -/
def limitRoles : Stack ≃ Stack := Equiv.swap 2 10
def firstMap (point : RankCompare.Label) : Label :=
  if point=0 then 0 else if point=1 then 1 else if point=2 then 2 else if point=3 then increment else second
def secondMap (point : RankCompare.Label) : Label :=
  if point=0 then second else if point=1 then 5 else if point=2 then 6 else if point=5 then clearRank else done
def copyMap : B23_4_RatWordPrep.WholeCopy.Label → Label
  | .boot => 8 | .copy => 9 | .restore => 10 | .done => done
def firstBody (point : RankCompare.Label) : Statement C :=
  LabelMap.statement firstMap (StackIso.statement limitRoles (RankCompare.program .halt .halt .halt point))
def secondBody (point : RankCompare.Label) : Statement C :=
  LabelMap.statement secondMap (RankCompare.program .halt .halt .halt point)
def copyLocal (point : B23_4_RatWordPrep.WholeCopy.Label) :
    TM2.Stmt Alphabet B23_4_RatWordPrep.WholeCopy.Label (Store C) :=
  StackIso.statement (BestUpdate.copyRoles false)
    (StoreIso.statement BestUpdate.storeIso (B23_4_RatWordPrep.WholeCopy.program .halt point))
def copyBody (point : B23_4_RatWordPrep.WholeCopy.Label) : Statement C := LabelMap.statement copyMap (copyLocal point)
def program (caller : Statement C) (point : Label) : Statement C :=
  if point=0 then firstBody 0 else if point=1 then firstBody 1 else if point=2 then firstBody 2
  else if point=increment then .push 9 (fun _ => true) (.goto (fun _ => second))
  else if point=second then secondBody 0 else if point=5 then secondBody 1 else if point=6 then secondBody 2
  else if point=clearRank then .pop 9 BestUpdate.capturePresent (.branch (fun memory => memory.2.1)
    (.goto (fun _ => clearRank)) (.goto (fun _ => copyMap .boot)))
  else if point=8 then copyBody .boot else if point=9 then copyBody .copy else if point=10 then copyBody .restore
  else if point=done then caller else .halt
/-- Ghost specification only; runtime selection uses physical presence branches. -/
def cappedSucc (limit value : Nat) : Nat := if value<limit then value+1 else value
def merged (limit sup skip : Nat) : Nat := min (cappedSucc limit sup) skip
def bank (bg : Stack → List Bool) (limit sup skip : Nat) : Stack → List Bool :=
  fun slot => if slot=9 then unary sup else if slot=10 then unary skip else if slot=2 then unary limit
    else if slot=7 then [] else if slot=12 then [] else bg slot
def state (point : Label) (memory : Store C) (slots : Stack → List Bool) : State C := ⟨some point,memory,slots⟩
def Work (slot : Stack) : Prop := slot=2 ∨ slot=7 ∨ slot=9 ∨ slot=10 ∨ slot=12

theorem first_code (caller : Statement C) (point : RankCompare.Label) (proper : RankCompare.Interior point) :
    program caller (firstMap point)=firstBody point := by
  fin_cases point <;> simp_all [RankCompare.Interior,firstMap,program]
theorem second_code (caller : Statement C) (point : RankCompare.Label) (proper : RankCompare.Interior point) :
    program caller (secondMap point)=secondBody point := by
  fin_cases point <;> simp_all [RankCompare.Interior,secondMap,program,increment,second]
theorem copy_code (caller : Statement C) (point : B23_4_RatWordPrep.WholeCopy.Label) (proper : point≠.done) :
    program caller (copyMap point)=copyBody point := by
  cases point <;> simp_all [copyMap,program,increment,second,clearRank]
theorem done_code (caller : Statement C) : program caller done=caller := rfl
private theorem closed (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro memory;exact Finset.mem_univ (target memory)
  | halt => trivial
theorem supports (caller : Statement C) : TM2.Supports (program caller) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun point _ => closed (program caller point)⟩
theorem finite_store [Finite C] : Finite (Store C) := inferInstance
end RootB236.Controller.RankMerge
