module
public import Common.PSTR_TM_B1PrepareTrace_070
public import Common.PSTR_TM_CounterFrame_064
public import Common.PSTR_TM_ShiftColumnTrace_066

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1LoopCode071
open PaperProofs.Common.Native.RationalControllerComputation

def compareLabel (q : Fin 21) : Fin 82 := ⟨q.val, by have h := q.isLt; omega⟩
def counterLabel (q : Fin 15) : Fin 82 := ⟨21 + q.val, by have h := q.isLt; omega⟩
def rewindBeforeLabel (q : Fin 6) : Fin 82 := ⟨36 + q.val, by have h := q.isLt; omega⟩
def shiftLabel (q : Fin 20) : Fin 82 := ⟨42 + q.val, by have h := q.isLt; omega⟩
def rewindAfterLabel (q : Fin 6) : Fin 82 := ⟨62 + q.val, by have h := q.isLt; omega⟩

def liftCompare (old : MachineState 20) : MachineState 81 := ⟨compareLabel old.q, old.Tape⟩
def liftCounter (old : MachineState 14) : MachineState 81 := ⟨counterLabel old.q, old.Tape⟩
def liftRewindBefore (old : MachineState 5) : MachineState 81 := ⟨rewindBeforeLabel old.q, old.Tape⟩
def liftShift (old : MachineState 19) : MachineState 81 := ⟨shiftLabel old.q, old.Tape⟩
def liftRewindAfter (old : MachineState 5) : MachineState 81 := ⟨rewindAfterLabel old.q, old.Tape⟩

/-- ONE fixed82-label proposed B1 loop, with branch decisions made ONLY
from the real comparator HALT control. Every sub-HALT transfer, counter
transport, rewind, input erasure and marker search is an actual instruction.
Positive-numerator termination and all trace/cost claims remain to prove. -/
def loopMachine : Machine 81 := fun q symbol =>
  if h0 : q.val < 21 then
    if q.val = 19 then some (68, .move .right)
    else if q.val = 18 ∨ q.val = 20 then some (74, .move .left)
    else (PSTRTMCompareCode054.compareMachine ⟨q.val, h0⟩ symbol).map
      (fun (next, statement) => (compareLabel next, statement))
  else if h1 : q.val < 36 then
    if q.val = 35 then some (71, .move .left)
    else (PSTRTMIncrement009.incrementMachine ⟨q.val - 21, by omega⟩ symbol).map
      (fun (next, statement) => (counterLabel next, statement))
  else if h2 : q.val < 42 then
    if q.val = 41 then some (42, .write symbol)
    else (PSTRTMColumnRewind067.rewindMachine ⟨q.val - 36, by omega⟩ symbol).map
      (fun (next, statement) => (rewindBeforeLabel next, statement))
  else if h3 : q.val < 62 then
    if q.val = 60 then some (62, .write symbol)
    else (PSTRTMShiftColumnCode065.shiftMachine ⟨q.val - 42, by omega⟩ symbol).map
      (fun (next, statement) => (shiftLabel next, statement))
  else if h4 : q.val < 68 then
    if q.val = 67 then some (0, .write symbol)
    else (PSTRTMColumnRewind067.rewindMachine ⟨q.val - 62, by omega⟩ symbol).map
      (fun (next, statement) => (rewindAfterLabel next, statement))
  else match q.val with
    | 68 => some (69, .move .right)
    | 69 => some (70, .move .right)
    | 70 => some (21, .move .right)
    | 71 => some (72, .move .left)
    | 72 => some (73, .move .left)
    | 73 => some (36, .move .left)
    | 74 => if symbol then some (75, .write false) else some (78, .move .right)
    | 75 => some (76, .move .left)
    | 76 => some (77, .write false)
    | 77 => some (74, .move .left)
    | 78 => if symbol then some (79, .write false) else some (78, .move .right)
    | 79 => some (80, .move .right)
    | 80 => some (81, .move .right)
    | _ => none

def state (q : Fin 82) (left right : List Bool) : MachineState 81 := ⟨q, Turing.Tape.mk₂ left right⟩

theorem loop_halt (left right : List Bool) : Turing.TM0.step loopMachine (state 81 left right) = none := by
  simp [Turing.TM0.step, loopMachine, state]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1LoopCode071
