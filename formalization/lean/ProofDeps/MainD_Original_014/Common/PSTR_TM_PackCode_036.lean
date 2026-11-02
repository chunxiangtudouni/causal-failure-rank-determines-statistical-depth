module
public import Common.PSTR_TM_AlignUnit_032
public import Common.PSTR_TM_PadTrace_035

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackCode036
open PaperProofs.Common.Native.RationalControllerComputation

def embedAlign (q : Fin 135) : Fin 194 := ⟨q.val + 10, by omega⟩
def embedPad (q : Fin 41) : Fin 194 := ⟨q.val + 145, by omega⟩
def liftAlign (old : MachineState 134) : MachineState 193 := ⟨embedAlign old.q, old.Tape⟩
def liftPad (old : MachineState 40) : MachineState 193 := ⟨embedPad old.q, old.Tape⟩

/-- Actual finite controller for isolated two-operand alignment. The
operand ends are read from real pair flags. A missing digit is allocated
as a flagged0 on the real blank tape; no runtime width or value is supplied.
The existing030 and034 programs retain their actual moves and writes.
Only their HALTs become head-preserving transfers. -/
def packMachine : Machine 193 := fun q symbol =>
  if q.val < 10 then
    match q.val with
    | 0 => some (if symbol then 2 else 1, .move .right)
    | 1 => some (if symbol then 10 else 3, if symbol then .move .left else .move .right)
    | 2 => some (if symbol then 10 else 145, .move .left)
    | 3 => some (4, .move .right)
    | 4 => some (5, .move .right)
    | 5 => some (if symbol then 7 else 6, .move .right)
    | 6 => if symbol then some (22, .move .left) else some (8, .move .left)
    | 7 => if symbol then some (23, .move .left) else none
    | 8 => some (9, .move .left)
    | _ => some (186, .move .left)
  else if h : q.val < 145 then
    if q.val = 144 then some (0, .write symbol)
    else if q.val = 18 ∧ symbol = false then some (193, .write true)
    else (PSTRTMAlignCode030.alignMachine ⟨q.val - 10, by omega⟩ symbol).map
      (fun (next, statement) => (embedAlign next, statement))
  else if h : q.val < 186 then
    if q.val = 185 then some (0, .write symbol)
    else (PSTRTMPadInsert034.padMachine ⟨q.val - 145, by omega⟩ symbol).map
      (fun (next, statement) => (embedPad next, statement))
  else
    match q.val with
    | 186 => some (187, .write false)
    | 187 => some (188, .move .left)
    | 188 => some (189, .move .left)
    | 189 => some (190, .move .left)
    | 190 => some (if symbol then 191 else 192, if symbol then .move .left else .move .right)
    | 191 => some (190, .move .left)
    | 193 => some (24, .move .left)
    | _ => none

def state (q : Fin 194) (left right : List Bool) : MachineState 193 := ⟨q, Turing.Tape.mk₂ left right⟩

theorem pack_halt (left right : List Bool) :
    Turing.TM0.step packMachine (state 192 left right) = none := by
  simp [Turing.TM0.step, packMachine, state]

/-- Ghost specification of the actual zero extension. Each recursive
step consumes an actual operand digit, including when the other end is blank. -/
def digitPairs : List Bool → List Bool → List (Bool × Bool)
  | [], [] => []
  | a :: first, [] => (a, false) :: digitPairs first []
  | [], b :: second => (false, b) :: digitPairs [] second
  | a :: first, b :: second => (a, b) :: digitPairs first second

theorem digitPairs_length (first second : List Bool) :
    (digitPairs first second).length = max first.length second.length := by
  induction first generalizing second with
  | nil =>
    induction second with
    | nil => simp [digitPairs]
    | cons b second ih => simpa [digitPairs] using congrArg Nat.succ ih
  | cons a first ih =>
    cases second with
    | nil => simpa [digitPairs] using congrArg Nat.succ (ih [])
    | cons b second => simpa [digitPairs, Nat.succ_max_succ] using congrArg Nat.succ (ih second)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackCode036
