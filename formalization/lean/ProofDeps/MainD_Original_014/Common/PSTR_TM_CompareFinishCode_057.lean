module
public import Common.PSTR_TM_CompareValue_056

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompareFinishCode057
open PaperProofs.Common.Native.RationalControllerComputation

def embedKernel (q : Fin 21) : Fin 53 := ⟨q.val, by omega⟩
def liftKernel (old : MachineState 20) : MachineState 52 := ⟨embedKernel old.q, old.Tape⟩
def eraseFlag (relation : Fin 3) : Fin 53 := ⟨21 + 4 * relation.val, by have h := relation.isLt; omega⟩
def dataLeft (relation : Fin 3) : Fin 53 := ⟨22 + 4 * relation.val, by have h := relation.isLt; omega⟩
def eraseData (relation : Fin 3) : Fin 53 := ⟨23 + 4 * relation.val, by have h := relation.isLt; omega⟩
def nextFlag (relation : Fin 3) : Fin 53 := ⟨24 + 4 * relation.val, by have h := relation.isLt; omega⟩
def writer (relation : Fin 3) (phase : Fin 6) : Fin 53 :=
  ⟨33 + 6 * relation.val + phase.val, by have h := relation.isLt; have hp := phase.isLt; omega⟩

/-- Actual53-label isolated comparison/output program. All old kernel
nonhalting instructions remain. Its computed HALT relation moves left into
a real flag/data eraser, then writes canonical Nat Bool and rewinds to it. -/
def resultMachine : Machine 52 := fun q symbol =>
  if h0 : q.val < 18 then
    (PSTRTMCompareCode054.compareMachine ⟨q.val, by omega⟩ symbol).map
      (fun (next, statement) => (embedKernel next, statement))
  else if h1 : q.val < 21 then
    some (eraseFlag ⟨q.val - 18, by omega⟩, .move .left)
  else if h2 : q.val < 33 then
    let relation : Fin 3 := ⟨(q.val - 21) / 4, by omega⟩
    match (q.val - 21) % 4 with
    | 0 => if symbol then some (⟨q.val + 1, by omega⟩, .write false) else some (writer relation 0, .move .right)
    | 1 => some (⟨q.val + 1, by omega⟩, .move .left)
    | 2 => some (⟨q.val + 1, by omega⟩, .write false)
    | _ => some (eraseFlag relation, .move .left)
  else if h3 : q.val < 51 then
    let relation : Fin 3 := ⟨(q.val - 33) / 6, by omega⟩
    match (q.val - 33) % 6 with
    | 0 => some (⟨q.val + 1, by omega⟩, .write true)
    | 1 => some (⟨q.val + 1, by omega⟩, .move .right)
    | 2 => some (⟨q.val + 1, by omega⟩, .write false)
    | 3 => some (⟨q.val + 1, by omega⟩, .move .right)
    | 4 => some (⟨q.val + 1, by omega⟩, .write (PSTRTMCompareValue056.resultLe relation))
    | _ => some (51, .move .left)
  else if q.val = 51 then some (52, .move .left) else none

def state (q : Fin 53) (left right : List Bool) : MachineState 52 := ⟨q, Turing.Tape.mk₂ left right⟩
def outputWord (relation : Fin 3) : List Bool := [true,false,PSTRTMCompareValue056.resultLe relation]

theorem result_halt (left right : List Bool) :
    Turing.TM0.step resultMachine (state 52 left right) = none := by
  simp [Turing.TM0.step, resultMachine, state]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompareFinishCode057
