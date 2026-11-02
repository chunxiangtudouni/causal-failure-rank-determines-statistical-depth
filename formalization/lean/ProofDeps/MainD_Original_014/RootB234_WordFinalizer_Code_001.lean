module

public import Common.PSTR_WordBool_RatInputAPI_093

/-! Fixed three-label output finalizer. An actual Option-presence test clears
old stack 0, reverses all of stack 13 into empty stack 3, and reverses 3 into
0. FALSE is data. The final empty read executes HALT, rather than a done port.
The caller context is lifted by the already verified ContextLift machine. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.WordFinalizer

open Turing
open PaperProofs.Common.Native.PSTRWordBool

abbrev Stack := RatInput.Stack
abbrev Alphabet := RatInput.Alphabet
abbrev Registers := Bool × Bool

inductive Label where
  | clear | collect | restore
  deriving DecidableEq

instance : Fintype Label where
  elems := {.clear,.collect,.restore}
  complete := by intro point; cases point <;> simp

instance : Inhabited Label := ⟨.clear⟩

abbrev Store (C : Type*) := C × Registers
abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Store C)

def capture (_memory : Registers) (cell : Option Bool) : Registers :=
  (cell.isSome, cell.getD false)

def baseProgram : Label → TM2.Stmt Alphabet Label Registers
  | .clear => .pop 0 capture (.branch Prod.fst
      (.goto (fun _ => .clear)) (.goto (fun _ => .collect)))
  | .collect => .pop 13 capture (.branch Prod.fst
      (.push 3 Prod.snd (.goto (fun _ => .collect))) (.goto (fun _ => .restore)))
  | .restore => .pop 3 capture (.branch Prod.fst
      (.push 0 Prod.snd (.goto (fun _ => .restore))) .halt)

def program {C : Type*} : Label → Statement C := ContextLift.machine baseProgram

def support : Finset Label := Finset.univ

private theorem supports_univ_stmt {C : Type*} (body : Statement C) :
    TM2.SupportsStmt support body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _; simp [support]
  | halt => trivial

theorem supports {C : Type*} : TM2.Supports (program (C := C)) support :=
  ⟨by simp [support],fun _ _ => supports_univ_stmt _⟩

def cells (frame : Stack → List Bool) (out parked source : List Bool) : Stack → List Bool :=
  fun slot => if slot=0 then out else if slot=3 then parked else if slot=13 then source else frame slot

def state {C : Type*} (frame : Stack → List Bool) (point : Label) (memory : Store C)
    (out parked source : List Bool) : State C :=
  ⟨some point,memory,cells frame out parked source⟩

def entry {C : Type*} (frame : Stack → List Bool) (memory : Store C)
    (old bits : List Bool) : State C := state frame .clear memory old [] bits

def result {C : Type*} (frame : Stack → List Bool) (context : C) (bits : List Bool) : State C :=
  ⟨none,(context,false,false),cells frame bits [] []⟩

theorem at_zero (frame : Stack → List Bool) (out parked source : List Bool) :
    cells frame out parked source 0=out := rfl

theorem at_three (frame : Stack → List Bool) (out parked source : List Bool) :
    cells frame out parked source 3=parked := rfl

theorem at_thirteen (frame : Stack → List Bool) (out parked source : List Bool) :
    cells frame out parked source 13=source := rfl

theorem frame_at (frame : Stack → List Bool) (out parked source : List Bool)
    (slot : Stack) (n0 : slot≠0) (n3 : slot≠3) (n13 : slot≠13) :
    cells frame out parked source slot=frame slot := by
  simp only [cells,n0,n3,n13,ite_false]

theorem update_zero (frame : Stack → List Bool) (out parked source next : List Bool) :
    Function.update (cells frame out parked source) 0 next=cells frame next parked source := by
  funext slot; fin_cases slot <;> rfl

theorem update_three (frame : Stack → List Bool) (out parked source next : List Bool) :
    Function.update (cells frame out parked source) 3 next=cells frame out next source := by
  funext slot; fin_cases slot <;> rfl

theorem update_thirteen (frame : Stack → List Bool) (out parked source next : List Bool) :
    Function.update (cells frame out parked source) 13 next=cells frame out parked next := by
  funext slot; fin_cases slot <;> rfl

variable {C : Type*}

theorem clear_bit (frame : Stack → List Bool) (memory : Store C)
    (digit : Bool) (out parked source : List Bool) :
    TM2.step program (state frame .clear memory (digit::out) parked source)=
      some (state frame .clear (memory.1,true,digit) out parked source) := by
  simp [program,ContextLift.machine,ContextLift.statement,baseProgram,state,
    TM2.step,TM2.stepAux,capture,at_zero,update_zero]

theorem clear_end (frame : Stack → List Bool) (memory : Store C) (parked source : List Bool) :
    TM2.step program (state frame .clear memory [] parked source)=
      some (state frame .collect (memory.1,false,false) [] parked source) := by
  simp [program,ContextLift.machine,ContextLift.statement,baseProgram,state,
    TM2.step,TM2.stepAux,capture,at_zero,update_zero]

theorem collect_bit (frame : Stack → List Bool) (memory : Store C)
    (digit : Bool) (out parked source : List Bool) :
    TM2.step program (state frame .collect memory out parked (digit::source))=
      some (state frame .collect (memory.1,true,digit) out (digit::parked) source) := by
  simp [program,ContextLift.machine,ContextLift.statement,baseProgram,state,
    TM2.step,TM2.stepAux,capture,at_thirteen,at_three,update_thirteen,update_three]

theorem collect_end (frame : Stack → List Bool) (memory : Store C) (out parked : List Bool) :
    TM2.step program (state frame .collect memory out parked [])=
      some (state frame .restore (memory.1,false,false) out parked []) := by
  simp [program,ContextLift.machine,ContextLift.statement,baseProgram,state,
    TM2.step,TM2.stepAux,capture,at_thirteen,update_thirteen]

theorem restore_bit (frame : Stack → List Bool) (memory : Store C)
    (digit : Bool) (out parked source : List Bool) :
    TM2.step program (state frame .restore memory out (digit::parked) source)=
      some (state frame .restore (memory.1,true,digit) (digit::out) parked source) := by
  simp [program,ContextLift.machine,ContextLift.statement,baseProgram,state,
    TM2.step,TM2.stepAux,capture,at_three,at_zero,update_three,update_zero]

theorem restore_end (frame : Stack → List Bool) (memory : Store C) (out source : List Bool) :
    TM2.step program (state frame .restore memory out [] source)=
      some (⟨none,(memory.1,false,false),cells frame out [] source⟩ : State C) := by
  simp [program,ContextLift.machine,ContextLift.statement,baseProgram,state,
    TM2.step,TM2.stepAux,capture,at_three,update_three]

theorem result_halt (frame : Stack → List Bool) (context : C) (bits : List Bool) :
    TM2.step program (result frame context bits)=none := rfl

end RootB234.WordFinalizer
