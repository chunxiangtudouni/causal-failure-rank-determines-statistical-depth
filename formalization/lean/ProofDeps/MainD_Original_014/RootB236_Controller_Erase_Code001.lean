module

public import Common.PSTR_WordBool_AuxWorkspace_020
public import Common.PSTR_WordBool_ScannerClock_024
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.List.Chain

/-! Actual fixed finite-mask erase. A unary selected-tool counter is consumed
while the skipped mask prefix is physically parked, then restored together
with that prefix. No runtime tool index occurs in finite control. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB236.Controller.Erase

open Turing PaperProofs.Common.Native.PSTRWordBool

abbrev Stack := Fin 16
abbrev Label := Fin 2
abbrev Alphabet (_ : Stack) := Bool
abbrev Store (C : Type*) := C × Bool × Bool
abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Store C)

variable {C : Type*}

def capturePresent (memory : Store C) (value : Option Bool) : Store C :=
  (memory.1, value.isSome, memory.2.2)

def captureBit (memory : Store C) (value : Option Bool) : Store C :=
  (memory.1, memory.2.1, value.getD false)

def capture (memory : Store C) (value : Option Bool) : Store C :=
  (memory.1, value.isSome, value.getD false)

def program (point : Label) : Statement C :=
  if point = 0 then
    .pop 5 capturePresent (.branch (fun memory => memory.2.1)
      (.pop 4 captureBit (.push 7 (fun memory => memory.2.2) (.goto (fun _ => 0))))
      (.pop 4 captureBit (.push 4 (fun _ => false) (.goto (fun _ => 1)))))
  else
    .pop 7 capture (.branch (fun memory => memory.2.1)
      (.push 4 (fun memory => memory.2.2) (.push 5 (fun _ => true) (.goto (fun _ => 1))))
      .halt)

def cells (background : Stack → List Bool) (mask count parked : List Bool)
    (point : Stack) : List Bool :=
  if point = 4 then mask else if point = 5 then count else if point = 7 then parked
  else background point

def state (background : Stack → List Bool) (point : Option Label) (memory : Store C)
    (mask count parked : List Bool) : State C :=
  ⟨point, memory, cells background mask count parked⟩

theorem cells_frame (background : Stack → List Bool) (mask count parked : List Bool)
    (point : Stack) (notMask : point ≠ 4) (notCount : point ≠ 5) (notParked : point ≠ 7) :
    cells background mask count parked point = background point := by
  simp [cells, notMask, notCount, notParked]

theorem step_walk (background : Stack → List Bool) (context : C) (present saved bit : Bool)
    (mask count parked : List Bool) :
    TM2.step program (state background (some 0) (context,present,saved)
      (bit::mask) (true::count) parked) =
      some (state background (some 0) (context,true,bit) mask count (bit::parked)) := by
  change some (⟨some 0, (context,true,bit), _⟩ : State C) = _
  congr 1
  congr 1
  funext point
  fin_cases point <;> rfl

theorem step_erase (background : Stack → List Bool) (context : C) (present saved head : Bool)
    (suffix parked : List Bool) :
    TM2.step program (state background (some 0) (context,present,saved)
      (head::suffix) [] parked) =
      some (state background (some 1) (context,false,head) (false::suffix) [] parked) := by
  change some (⟨some 1, (context,false,head), _⟩ : State C) = _
  congr 1
  congr 1
  funext point
  fin_cases point <;> rfl

theorem step_restore (background : Stack → List Bool) (context : C) (present saved bit : Bool)
    (mask count parked : List Bool) :
    TM2.step program (state background (some 1) (context,present,saved)
      mask count (bit::parked)) =
      some (state background (some 1) (context,true,bit) (bit::mask) (true::count) parked) := by
  change some (⟨some 1, (context,true,bit), _⟩ : State C) = _
  congr 1
  congr 1
  funext point
  fin_cases point <;> rfl

theorem step_halt (background : Stack → List Bool) (context : C) (present saved : Bool)
    (mask count : List Bool) :
    TM2.step program (state background (some 1) (context,present,saved) mask count []) =
      some (state background none (context,false,false) mask count []) := by
  change some (⟨none, (context,false,false), _⟩ : State C) = _
  congr 1
  congr 1
  funext point
  fin_cases point <;> rfl

theorem program_actions (point : Label) : ScannerClock.actions (program (C := C) point) ≤ 3 := by
  fin_cases point <;> norm_num [program, ScannerClock.actions]

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C := C) point) ≤ 2 := by
  fin_cases point <;> norm_num [program, AuxWorkspace.pushes]

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C := C)) (Finset.univ : Finset Label) := by
  exact ⟨Finset.mem_univ _, fun point _ => supports_stmt (program point)⟩

end RootB236.Controller.Erase
