module
public import RootB236_Controller_Erase_Public004

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.ErasePort
open Turing PaperProofs.Common.Native.PSTRWordBool
abbrev Stack := Erase.Stack
abbrev Alphabet := Erase.Alphabet
abbrev Store := Erase.Store
abbrev Label := Fin 3
abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Store C)
variable {C : Type*}

def label (point : Erase.Label) : Label := point.castSucc
def position : Option Erase.Label → Label
  | none => 2
  | some point => label point
/-- In particular old HALT is represented by an ACTIVE return, not none. -/
def configuration (current : Erase.State C) : State C :=
  ⟨some (position current.l),current.var,current.stk⟩

/-- Static source transformation. Every old HALT executes a real goto2. -/
def body : Erase.Statement C → Statement C
  | .push point value next => .push point value (body next)
  | .peek point value next => .peek point value (body next)
  | .pop point value next => .pop point value (body next)
  | .load value next => .load value (body next)
  | .branch test yes no => .branch test (body yes) (body no)
  | .goto target => .goto (fun memory => label (target memory))
  | .halt => .goto (fun _ => 2)
def program (caller : Statement C) (point : Label) : Statement C :=
  if point=0 then body (Erase.program 0) else if point=1 then body (Erase.program 1) else caller

theorem code_at (caller : Statement C) (point : Erase.Label) :
    program caller (label point)=body (Erase.program point) := by fin_cases point <;> rfl
theorem at_port (caller : Statement C) : program caller 2=caller := rfl
theorem halted_to_active (current : Erase.State C) (halted : current.l=none) :
    (configuration current).l=some 2 := by simp only [configuration,halted,position]
theorem port_iff (current : Erase.State C) : (configuration current).l=some 2 ↔ current.l=none := by
  cases current with
  | mk selected memory slots =>
    cases selected with
    | none => simp [configuration,position]
    | some selected => fin_cases selected <;> simp [configuration,position,label]

theorem stepAux_configuration (statement : Erase.Statement C) (memory : Store C)
    (slots : Stack → List Bool) :
    TM2.stepAux (body statement) memory slots=configuration (TM2.stepAux statement memory slots) := by
  induction statement generalizing memory slots with
  | push point value next ih => exact ih memory (Function.update slots point (value memory::slots point))
  | peek point value next ih => exact ih (value memory (slots point).head?) slots
  | pop point value next ih => exact ih (value memory (slots point).head?) (Function.update slots point (slots point).tail)
  | load value next ih => exact ih (value memory) slots
  | branch test yes no iy ino => cases choice : test memory <;> simp only [body,TM2.stepAux,choice,Bool.cond_false,Bool.cond_true]; exacts [ino memory slots,iy memory slots]
  | goto _ | halt => rfl

theorem edge_configuration (caller : Statement C) (before after : Erase.State C)
    (edge : TM2.step Erase.program before=some after) :
    TM2.step (program caller) (configuration before)=some (configuration after) := by
  cases before with
  | mk selected memory slots =>
    cases selected with
    | none => cases edge
    | some selected =>
      change some (TM2.stepAux (program caller (label selected)) memory slots)=_
      rw [code_at,stepAux_configuration]
      exact congrArg some (congrArg configuration (Option.some.inj edge))

theorem body_actions (statement : Erase.Statement C) : ScannerClock.actions (body statement)=ScannerClock.actions statement := by
  induction statement with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih => exact congrArg (·+1) ih
  | load _ _ ih => exact ih
  | branch _ _ _ iy ino => exact congrArg₂ max iy ino
  | goto _ | halt => rfl
theorem body_pushes (statement : Erase.Statement C) : AuxWorkspace.pushes (body statement)=AuxWorkspace.pushes statement := by
  induction statement with
  | push _ _ _ ih => exact congrArg (·+1) ih
  | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ iy ino => exact congrArg₂ max iy ino
  | goto _ | halt => rfl
theorem body_nodes (statement : Erase.Statement C) (memory : Store C) (slots : Stack → List Bool) :
    AuxWorkspace.nodes (body statement) memory slots=AuxWorkspace.nodes statement memory slots := by
  induction statement generalizing memory slots with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => simp only [body,AuxWorkspace.nodes,ih]
  | branch test yes no iy ino => cases choice : test memory <;> simp only [body,AuxWorkspace.nodes,choice,Bool.false_eq_true,ite_false,ite_true,iy,ino]
  | goto _ | halt => rfl
theorem body_clock (statement : Erase.Statement C) (memory : Store C) (slots : Stack → List Bool) :
    ScannerStatement.clock (body statement) memory slots=ScannerStatement.clock statement memory slots := by
  induction statement generalizing memory slots with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => simp only [body,ScannerStatement.clock,ih]
  | branch test yes no iy ino => cases choice : test memory <;> simp only [body,ScannerStatement.clock,choice,iy,ino]
  | goto _ | halt => rfl

private theorem closed_stmt (statement : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) statement := by
  induction statement with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ iy ino => exact ⟨iy,ino⟩
  | goto target => intro memory;exact Finset.mem_univ (target memory)
  | halt => trivial
theorem supports (caller : Statement C) : TM2.Supports (program caller) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun point _ => closed_stmt (program caller point)⟩
end RootB236.Controller.ErasePort
