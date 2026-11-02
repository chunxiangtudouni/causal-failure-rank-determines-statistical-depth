module

public import Structure.PA17_TM_Division_Loop_002a
public import Common.PSTR_TM_ColumnRewind_067
import Mathlib.Tactic.FinCases

/-! Fixed28-label source-fetch control. Archive columns are the SAME
four-cell format [sourceOrQ,true,pending,true], with a false left guard.
Three real false separators lie between the archive and resident firstR.
The kernel searches MSB-first for a real pending bit, physically returns to
firstR and halts with none/bit0/bit1 in finite control. It never receives a
width, source pointer, dividend, quotient or source-selection answer. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002

def returnLabel (mode : Fin 3) (phase : Fin 4) : Fin 28 :=
  ⟨10 + 4 * mode.val + phase.val, by have hm := mode.isLt; have hp := phase.isLt; omega⟩

def returnSource (mode : Fin 3) : Fin 28 := returnLabel mode 0
def returnFlagA (mode : Fin 3) : Fin 28 := returnLabel mode 1
def returnPending (mode : Fin 3) : Fin 28 := returnLabel mode 2
def returnFlagB (mode : Fin 3) : Fin 28 := returnLabel mode 3

def returnHop (mode : Fin 3) : Fin 28 := ⟨22 + mode.val, by omega⟩
def sourceHalt (mode : Fin 3) : Fin 28 := ⟨25 + mode.val, by omega⟩

def bitMode (bit : Bool) : Fin 3 := if bit then 2 else 1

def sourceMachine : Machine 27 := fun q symbol =>
  match q.val with
  | 0 => some (1, .move .left)
  | 1 => some (2, .move .left)
  | 2 => some (3, .move .left)
  | 3 => some (4, .move .left)
  | 4 => if symbol then some (5, .move .left) else some (returnSource 0, .move .right)
  | 5 => some (if symbol then 7 else 6, .move .left)
  | 6 => some (8, .move .left)
  | 7 => some (9, .move .left)
  | 8 => some (4, .move .left)
  | 9 => some (returnSource (bitMode symbol), .write symbol)
  | _ =>
    if hreturn : q.val < 22 then
      let mode : Fin 3 := ⟨(q.val - 10) / 4, by omega⟩
      match (q.val - 10) % 4 with
      | 0 => some (returnFlagA mode, .move .right)
      | 1 => if symbol then some (returnPending mode, .move .right) else some (returnHop mode, .move .right)
      | 2 => some (returnFlagB mode, .move .right)
      | _ => some (returnSource mode, .move .right)
    else if hhop : q.val < 25 then
      some (sourceHalt ⟨q.val - 22, by omega⟩, .move .right)
    else none

def sourceState (label : Fin 28) (left right : List Bool) : MachineState 27 :=
  ⟨label, Turing.Tape.mk₂ left right⟩

theorem source_halt (mode : Fin 3) (left right : List Bool) :
    Turing.TM0.step sourceMachine (sourceState (sourceHalt mode) left right) = none := by
  fin_cases mode <;> simp [Turing.TM0.step, sourceState, sourceHalt, sourceMachine]

theorem return_commands (mode : Fin 3) (a b : Bool) :
    sourceMachine (returnSource mode) a = some (returnFlagA mode, .move .right) ∧
    sourceMachine (returnFlagA mode) true = some (returnPending mode, .move .right) ∧
    sourceMachine (returnPending mode) b = some (returnFlagB mode, .move .right) ∧
    sourceMachine (returnFlagB mode) true = some (returnSource mode, .move .right) := by
  fin_cases mode <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem return_end_commands (mode : Fin 3) :
    sourceMachine (returnSource mode) false = some (returnFlagA mode, .move .right) ∧
    sourceMachine (returnFlagA mode) false = some (returnHop mode, .move .right) ∧
    sourceMachine (returnHop mode) false = some (sourceHalt mode, .move .right) := by
  fin_cases mode <;> exact ⟨rfl, rfl, rfl⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002
