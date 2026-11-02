module

public import Common.PSTR_WordBool_RatInputAPI_093

/-! Actual finite unary doubling/MSB Horner kernel for the structural
Word route.  Digits are popped from3, the TRUE accumulator lives on5 and
the actual doubling/restore workspace is6.  No Nat computation is loaded
into control.  The separate original Word-domain bounds must pay for the
produced unary value at the real original caller. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootL01.SymbolicSource.Unary

open Turing
open PaperProofs.Common.Native.PSTRWordBool

abbrev Stack := RatInput.Stack
abbrev Alphabet := RatInput.Alphabet
abbrev Registers := Bool × Bool
abbrev Store (C : Type*) := C × Registers

inductive Label where
  | read | double | restore | plainDouble | done
  deriving DecidableEq

instance : Fintype Label where
  elems := {.read,.double,.restore,.plainDouble,.done}
  complete := by intro point; cases point <;> simp

instance : Inhabited Label := ⟨.read⟩

abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Store C)
abbrev Bank := Stack → List Bool

def captureBit (_ : Registers) (cell : Option Bool) : Registers := (cell.getD false,cell.isSome)
def capturePresent (memory : Registers) (cell : Option Bool) : Registers := (memory.1,cell.isSome)

def baseProgram : Label → TM2.Stmt Alphabet Label Registers
  | .read => .pop 3 captureBit (.branch Prod.snd
      (.goto (fun _ => .double)) (.goto (fun _ => .done)))
  | .double => .pop 5 capturePresent (.branch Prod.snd
      (.push 6 (fun _ => true) (.push 6 (fun _ => true) (.goto (fun _ => .double))))
      (.goto (fun _ => .restore)))
  | .restore => .pop 6 capturePresent (.branch Prod.snd
      (.push 5 (fun _ => true) (.goto (fun _ => .restore)))
      (.branch Prod.fst (.push 5 (fun _ => true) (.goto (fun _ => .read))) (.goto (fun _ => .read))))
  | .plainDouble => .load (fun _ => (false,false)) (.goto (fun _ => .double))
  | .done => .halt

def program {C : Type*} (caller : Statement C) (point : Label) : Statement C :=
  if point = .done then caller else ContextLift.statement (baseProgram point)

def cells (frame : Bank) (digits value work : List Bool) : Bank :=
  fun slot => if slot = 3 then digits else if slot = 5 then value else if slot = 6 then work else frame slot

def state {C : Type*} (frame : Bank) (point : Label) (context : C) (memory : Registers)
    (digits value work : List Bool) : State C := ⟨some point,(context,memory),cells frame digits value work⟩

theorem digits_at (frame : Bank) (digits value work : List Bool) : cells frame digits value work 3 = digits := rfl
theorem value_at (frame : Bank) (digits value work : List Bool) : cells frame digits value work 5 = value := rfl
theorem work_at (frame : Bank) (digits value work : List Bool) : cells frame digits value work 6 = work := rfl

theorem update_digits (frame : Bank) (digits value work next : List Bool) :
    Function.update (cells frame digits value work) 3 next = cells frame next value work := by
  funext slot; fin_cases slot <;> rfl
theorem update_value (frame : Bank) (digits value work next : List Bool) :
    Function.update (cells frame digits value work) 5 next = cells frame digits next work := by
  funext slot; fin_cases slot <;> rfl
theorem update_work (frame : Bank) (digits value work next : List Bool) :
    Function.update (cells frame digits value work) 6 next = cells frame digits value next := by
  funext slot; fin_cases slot <;> rfl

variable {C : Type*}

theorem read_bit (caller : Statement C) (frame : Bank) (context : C) (memory : Registers)
    (digit : Bool) (digits value work : List Bool) :
    TM2.step (program caller) (state frame .read context memory (digit :: digits) value work) =
      some (state frame .double context (digit,true) digits value work) := by
  simp [program,baseProgram,ContextLift.statement,state,TM2.step,TM2.stepAux,captureBit,
    digits_at,update_digits]

theorem read_end (caller : Statement C) (frame : Bank) (context : C) (memory : Registers)
    (value work : List Bool) :
    TM2.step (program caller) (state frame .read context memory [] value work) =
      some (state frame .done context (false,false) [] value work) := by
  simp [program,baseProgram,ContextLift.statement,state,TM2.step,TM2.stepAux,captureBit,
    digits_at,update_digits]

theorem double_bit (caller : Statement C) (frame : Bank) (context : C) (bit flag : Bool)
    (digits value work : List Bool) :
    TM2.step (program caller) (state frame .double context (bit,flag) digits (true :: value) work) =
      some (state frame .double context (bit,true) digits value (true :: true :: work)) := by
  simp [program,baseProgram,ContextLift.statement,state,TM2.step,TM2.stepAux,capturePresent,
    value_at,work_at,update_value,update_work]

theorem double_end (caller : Statement C) (frame : Bank) (context : C) (bit flag : Bool)
    (digits work : List Bool) :
    TM2.step (program caller) (state frame .double context (bit,flag) digits [] work) =
      some (state frame .restore context (bit,false) digits [] work) := by
  simp [program,baseProgram,ContextLift.statement,state,TM2.step,TM2.stepAux,capturePresent,
    value_at,update_value]

theorem restore_bit (caller : Statement C) (frame : Bank) (context : C) (bit flag : Bool)
    (digits value work : List Bool) :
    TM2.step (program caller) (state frame .restore context (bit,flag) digits value (true :: work)) =
      some (state frame .restore context (bit,true) digits (true :: value) work) := by
  simp [program,baseProgram,ContextLift.statement,state,TM2.step,TM2.stepAux,capturePresent,
    value_at,work_at,update_value,update_work]

theorem restore_end (caller : Statement C) (frame : Bank) (context : C) (bit flag : Bool)
    (digits value : List Bool) :
    TM2.step (program caller) (state frame .restore context (bit,flag) digits value []) =
      some (state frame .read context (bit,false) digits (if bit then true :: value else value) []) := by
  cases bit <;>
    simp [program,baseProgram,ContextLift.statement,state,TM2.step,TM2.stepAux,capturePresent,
      value_at,work_at,update_value,update_work]

theorem plain_double_entry (caller : Statement C) (frame : Bank) (context : C) (memory : Registers)
    (digits value work : List Bool) :
    TM2.step (program caller) (state frame .plainDouble context memory digits value work) =
      some (state frame .double context (false,false) digits value work) := rfl

def support : Finset Label := Finset.univ

theorem supports_stmt (body : Statement C) : TM2.SupportsStmt support body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro memory; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C:=C) .halt) support :=
  ⟨Finset.mem_univ _,fun point _ => supports_stmt (program .halt point)⟩

theorem finiteStore [Finite C] : Finite (Store C) := inferInstance

theorem syntax_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point) ≤ 3 := by
  cases point <;> exact of_decide_eq_true rfl

theorem syntax_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point) ≤ 2 := by
  cases point <;> exact of_decide_eq_true rfl

end RootL01.SymbolicSource.Unary
