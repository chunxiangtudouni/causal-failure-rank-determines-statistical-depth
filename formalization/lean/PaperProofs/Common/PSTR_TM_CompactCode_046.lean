module
public import PaperProofs.Common.PSTR_TM_PadTrace_035
public import PaperProofs.Common.PSTR_TM_AddRun_026

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompactCode046
open PaperProofs.Common.Native.RationalControllerComputation

def embedCopy (q : Fin 41) : Fin 55 := ⟨q.val, by omega⟩
def liftCopy (old : MachineState 40) : MachineState 54 := ⟨embedCopy old.q, old.Tape⟩

/-- Remove the actual zero-B pair following each sum pair. The endmarker
is first allocated on real blank EOF. After each suffix copy it is moved
two cells left and its old1 is erased. The kept sum flag is a real transient
stop marker for the rewind; no source endpoint or loop count is supplied. -/
def compactMachine : Machine 54 := fun q symbol =>
  if q.val < 11 then
    match q.val with
    | 0 => some (1, .move .right)
    | 1 => some (if symbol then 0 else 2, if symbol then .move .right else .move .left)
    | 2 => some (3, .write true)
    | 3 => some (4, .move .left)
    | 4 => some (if symbol then 5 else 6, if symbol then .move .left else .move .right)
    | 5 => some (4, .move .left)
    | 6 => some (7, .move .right)
    | 7 => some (if symbol then 8 else 50, if symbol then .write false else .move .left)
    | 8 => some (9, .move .right)
    | 9 => some (10, .move .right)
    | _ => some (17, .move .right)
  else if h : 17 ≤ q.val ∧ q.val < 32 then
    (PSTRTMPadInsert034.padMachine ⟨q.val, by omega⟩ symbol).map
      (fun (next, statement) => (embedCopy next, statement))
  else
    match q.val with
    | 36 => some (37, .write false)
    | 37 => some (38, .move .left)
    | 38 => some (39, .write false)
    | 39 => some (40, .move .left)
    | 40 => some (41, .write true)
    | 41 => some (42, .move .left)
    | 42 => some (if symbol then 43 else 44, if symbol then .move .left else .write true)
    | 43 => some (42, .move .left)
    | 44 => some (6, .move .right)
    | 50 => some (51, .write false)
    | 51 => some (52, .move .left)
    | 52 => some (if symbol then 53 else 54, if symbol then .move .left else .move .right)
    | 53 => some (52, .move .left)
    | _ => none

def state (q : Fin 55) (left right : List Bool) : MachineState 54 := ⟨q, Turing.Tape.mk₂ left right⟩

theorem compact_halt (left right : List Bool) :
    Turing.TM0.step compactMachine (state 54 left right) = none := by
  simp [Turing.TM0.step, compactMachine, state]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompactCode046
