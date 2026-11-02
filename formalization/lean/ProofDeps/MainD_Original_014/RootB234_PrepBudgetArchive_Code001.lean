module

public import Common.PSTR_SYM_RatExportRun_094
public import Common.PSTR_WordBool_AuxWorkspace_020
public import Common.PSTR_WordBool_ScannerClock_024
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.List.Chain

/-! Consume the last paired rational archive and emit the existing RatExport
packet. The preceding datum marker is physically read and restored. One
delayed Bool distinguishes the last numerator bit from the sign; no width,
host number, prepared answer, or unbounded runtime register is used. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepBudgetArchive

open Turing PaperProofs.Common.Native.PSTRWordBool

abbrev Stack := Fin 16
abbrev Label := Fin 5
abbrev Alphabet (_ : Stack) := Bool
abbrev Store (C : Type*) := C × Bool × Bool × Bool
abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Store C)

variable {C : Type*}

def captureBit (memory : Store C) (value : Option Bool) : Store C :=
  (memory.1,value.getD false,memory.2.2.1,memory.2.2.2)

def captureFlag (memory : Store C) (value : Option Bool) : Store C :=
  (memory.1,memory.2.1,value.getD false,memory.2.2.2)

def remember (memory : Store C) : Store C :=
  (memory.1,memory.2.1,memory.2.2.1,memory.2.1)

def program (caller : Statement C) (point : Label) : Statement C :=
  if point = 0 then
    .pop 1 (fun memory _ => memory) (.pop 1 (fun memory _ => memory)
      (.push 15 (fun _ => false) (.push 15 (fun _ => false) (.goto (fun _ => 1)))))
  else if point = 1 then
    .pop 1 captureBit (.pop 1 captureFlag
      (.push 15 (fun memory => memory.2.1) (.push 15 (fun _ => true)
        (.branch (fun memory => memory.2.2.1)
          (.push 15 (fun _ => false) (.push 15 (fun _ => false) (.goto (fun _ => 2))))
          (.goto (fun _ => 1))))))
  else if point = 2 then
    .pop 1 captureBit (.pop 1 captureFlag (.load remember (.goto (fun _ => 3))))
  else if point = 3 then
    .pop 1 captureBit (.pop 1 captureFlag
      (.branch (fun memory => memory.2.2.1)
        (.push 1 (fun _ => true) (.push 1 (fun memory => memory.2.1)
          (.push 15 (fun memory => memory.2.2.2) (.push 15 (fun _ => true) (.goto (fun _ => 4))))))
        (.push 15 (fun memory => memory.2.2.2) (.push 15 (fun _ => true)
          (.load remember (.goto (fun _ => 3)))))))
  else caller

def backCells (digits : List Bool) : List Bool := digits.flatMap (fun bit => [bit,false])

def frontCells (digits : List Bool) : List Bool := digits.flatMap (fun bit => [true,bit])

def bank (background : Stack → List Bool) (source target : List Bool) : Stack → List Bool :=
  fun point => if point = 1 then source else if point = 15 then target else background point

def state (background : Stack → List Bool) (point : Label) (context : C)
    (bit flag pending : Bool) (source target : List Bool) : State C :=
  ⟨some point,(context,bit,flag,pending),bank background source target⟩

theorem step_entry (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag pending : Bool) (source target : List Bool) :
    TM2.step (program caller) (state background 0 context bit flag pending (true::true::source) target) =
      some (state background 1 context bit flag pending source (false::false::target)) := by
  change some (⟨some 1,(context,bit,flag,pending),_⟩ : State C) = _
  congr 1; congr 1
  funext point; fin_cases point <;> rfl

theorem step_den_later (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag pending digit : Bool) (source target : List Bool) :
    TM2.step (program caller) (state background 1 context bit flag pending (digit::false::source) target) =
      some (state background 1 context digit false pending source (true::digit::target)) := by
  change some (⟨some 1,(context,digit,false,pending),_⟩ : State C) = _
  congr 1; congr 1
  funext point; fin_cases point <;> rfl

theorem step_den_first (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag pending digit : Bool) (source target : List Bool) :
    TM2.step (program caller) (state background 1 context bit flag pending (digit::true::source) target) =
      some (state background 2 context digit true pending source (false::false::true::digit::target)) := by
  change some (⟨some 2,(context,digit,true,pending),_⟩ : State C) = _
  congr 1; congr 1
  funext point; fin_cases point <;> rfl

theorem step_num_first (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag pending digit : Bool) (source target : List Bool) :
    TM2.step (program caller) (state background 2 context bit flag pending (digit::false::source) target) =
      some (state background 3 context digit false digit source target) := by
  change some (⟨some 3,(context,digit,false,digit),_⟩ : State C) = _
  congr 1; congr 1
  funext point; fin_cases point <;> rfl

theorem step_num_later (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag pending digit : Bool) (source target : List Bool) :
    TM2.step (program caller) (state background 3 context bit flag pending (digit::false::source) target) =
      some (state background 3 context digit false digit source (true::pending::target)) := by
  change some (⟨some 3,(context,digit,false,digit),_⟩ : State C) = _
  congr 1; congr 1
  funext point; fin_cases point <;> rfl

theorem step_boundary (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag pending boundary : Bool) (source target : List Bool) :
    TM2.step (program caller) (state background 3 context bit flag pending (boundary::true::source) target) =
      some (state background 4 context boundary true pending (boundary::true::source) (true::pending::target)) := by
  change some (⟨some 4,(context,boundary,true,pending),_⟩ : State C) = _
  congr 1; congr 1
  funext point; fin_cases point <;> rfl

theorem program_actions (caller : Statement C) (point : Label) (active : point ≠ 4) :
    ScannerClock.actions (program caller point) ≤ 6 := by
  fin_cases point <;> norm_num [program,ScannerClock.actions] at *

theorem program_pushes (caller : Statement C) (point : Label) (active : point ≠ 4) :
    AuxWorkspace.pushes (program caller point) ≤ 4 := by
  fin_cases point <;> norm_num [program,AuxWorkspace.pushes] at *

private theorem supports_stmt (body : Statement C) :
    TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports (caller : Statement C) : TM2.Supports (program caller) (Finset.univ : Finset Label) := by
  exact ⟨Finset.mem_univ _, fun point _ => supports_stmt (program caller point)⟩

end RootB234.PrepBudgetArchive
