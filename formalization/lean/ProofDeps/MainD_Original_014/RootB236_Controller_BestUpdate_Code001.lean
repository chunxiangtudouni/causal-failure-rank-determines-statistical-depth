module
public import RootB236_Controller_RankCompare_Resources003
public import B23_4_RatWordPrep_SeqCmp_WholeCopyPublic_045
public import Common.PSTR_WordBool_StoreIso_048

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.BestUpdate
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
abbrev Stack := Fin 16
abbrev Label := Fin 13
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := RankCompare.Store
abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Store C)
variable {C : Type*}
def unary := RankCompare.unary
def boot : Label := 0
def clearRank : Label := 1
def clearTool : Label := 2
def done : Label := 3
def compareMap (point : RankCompare.Label) : Label :=
  if point=0 then 4 else if point=1 then 5 else if point=2 then 6 else if point=3 then clearRank else done
def copyMap (tool : Bool) : B23_4_RatWordPrep.WholeCopy.Label → Label
  | .boot => if tool then 10 else 7
  | .copy => if tool then 11 else 8
  | .restore => if tool then 12 else 9
  | .done => if tool then done else 10
/-- Static swaps of fixed physical roles, never a runtime movement. -/
def copyRoles (tool : Bool) : Stack ≃ Stack :=
  if tool then (Equiv.swap 0 5).trans ((Equiv.swap 2 14).trans (Equiv.swap 3 12))
  else (Equiv.swap 0 10).trans ((Equiv.swap 2 9).trans (Equiv.swap 3 12))
def storeIso : B23_4_RatWordPrep.WholeCopy.Store (C×Ordering) ≃ Store C where
  toFun memory := (memory.1.1,memory.2.1,memory.2.2,memory.1.2)
  invFun memory := ((memory.1,memory.2.2.2),memory.2.1,memory.2.2.1)
  left_inv := by intro memory;rcases memory with ⟨⟨context,order⟩,first,second⟩;rfl
  right_inv := by intro memory;rcases memory with ⟨context,first,second,order⟩;rfl

def copyBody (tool : Bool) (point : B23_4_RatWordPrep.WholeCopy.Label) : Statement C :=
  LabelMap.statement (copyMap tool) (StackIso.statement (copyRoles tool)
    (StoreIso.statement storeIso (B23_4_RatWordPrep.WholeCopy.program .halt point)))
def compareBody (point : RankCompare.Label) : Statement C :=
  LabelMap.statement compareMap (RankCompare.program .halt .halt .halt point)
def captureFlag (memory : Store C) (value : Option Bool) : Store C :=
  (memory.1,value.getD false,memory.2.2.1,memory.2.2.2)
def capturePresent (memory : Store C) (value : Option Bool) : Store C :=
  (memory.1,value.isSome,memory.2.2.1,memory.2.2.2)
def program (caller : Statement C) (point : Label) : Statement C :=
  if point=boot then
    .pop 13 captureFlag (.push 13 (fun _ => true) (.branch (fun memory => memory.2.1)
      (.goto (fun _ => compareMap 0)) (.goto (fun _ => clearRank))))
  else if point=clearRank then
    .pop 9 capturePresent (.branch (fun memory => memory.2.1)
      (.goto (fun _ => clearRank)) (.goto (fun _ => clearTool)))
  else if point=clearTool then
    .pop 14 capturePresent (.branch (fun memory => memory.2.1)
      (.goto (fun _ => clearTool)) (.goto (fun _ => copyMap false .boot)))
  else if point=done then caller
  else if point=4 then compareBody 0
  else if point=5 then compareBody 1
  else if point=6 then compareBody 2
  else if point=7 then copyBody false .boot
  else if point=8 then copyBody false .copy
  else if point=9 then copyBody false .restore
  else if point=10 then copyBody true .boot
  else if point=11 then copyBody true .copy
  else copyBody true .restore

def Work (slot : Stack) : Prop := slot=5 ∨ slot=7 ∨ slot=9 ∨ slot=10 ∨ slot=12 ∨ slot=13 ∨ slot=14
def bank (background : Stack → List Bool) (oldRank newRank tool : Nat)
    (oldBest : List Bool) (hasBest : Bool) (tail : List Bool) : Stack → List Bool :=
  fun slot => if slot=9 then unary oldRank else if slot=10 then unary newRank else
    if slot=5 then unary tool else if slot=14 then oldBest else if slot=13 then hasBest::tail else
    if slot=7 then [] else if slot=12 then [] else background slot
def state (point : Label) (memory : Store C) (slots : Stack → List Bool) : State C := ⟨some point,memory,slots⟩
def selected (hasBest : Bool) (oldRank newRank : Nat) : Prop := hasBest=false ∨ oldRank<newRank
instance selectedDecidable (hasBest : Bool) (oldRank newRank : Nat) : Decidable (selected hasBest oldRank newRank) :=
  inferInstanceAs (Decidable (hasBest=false ∨ oldRank<newRank))
def resultBank (background : Stack → List Bool) (oldRank newRank tool : Nat)
    (oldBest : List Bool) (hasBest : Bool) (tail : List Bool) : Stack → List Bool :=
  bank background (if selected hasBest oldRank newRank then newRank else oldRank) newRank tool
    (if selected hasBest oldRank newRank then unary tool else oldBest) true tail

theorem compare_code (caller : Statement C) (point : RankCompare.Label) (proper : RankCompare.Interior point) :
    program caller (compareMap point)=compareBody point := by
  fin_cases point <;> simp_all [RankCompare.Interior,compareMap,program,boot,clearRank,clearTool,done]
theorem copy_code (caller : Statement C) (tool : Bool) (point : B23_4_RatWordPrep.WholeCopy.Label)
    (proper : point≠.done) : program caller (copyMap tool point)=copyBody tool point := by
  cases tool <;> cases point <;> simp_all [copyMap,program,boot,clearRank,clearTool,done]
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
end RootB236.Controller.BestUpdate
