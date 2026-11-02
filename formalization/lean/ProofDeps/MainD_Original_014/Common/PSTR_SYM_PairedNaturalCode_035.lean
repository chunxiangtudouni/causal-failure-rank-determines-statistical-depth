module

public import Common.PSTR_SYM_DatumRun_034

/-! Candidate executable12-label in-place Natural record compactor.
The real RunsFrom/wholeTape proof is a separate next dependency. This source
alone is NOT an asserted producer or a completed preserving raw scanner. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPairedArchive

open Turing

/-- Navigation/data pairs use existing flag redundancy, not new cells or
an alternative original output encoding. The last pair is end/kind. -/
def naturalWord (digits : List Bool) : List Bool :=
  digits.flatMap (fun bit => [false,bit]) ++ [true,false]

def naturalCompactMachine : Machine 11 := fun label symbol =>
  match label.val with
  | 0 => some (1, .move .left)
  | 1 => some (2, .move .left)
  | 2 => some (3, .move .left)
  | 3 => some (4, .move .left)
  | 4 => if symbol then some (5, .write false) else some (7, .move .right)
  | 5 => some (6, .move .left)
  | 6 => some (4, .move .left)
  | 7 => some (8, .move .right)
  | 8 => if symbol then some (10, .move .right) else some (9, .move .right)
  | 9 => some (8, .move .right)
  | 10 => some (11, .move .right)
  | _ => none

def state (label : Fin 12) (left right : List Bool) : MachineState 11 :=
  ⟨label,Tape.mk₂ left right⟩

theorem naturalWord_cons (bit : Bool) (later : List Bool) :
    naturalWord (bit :: later) = false :: bit :: naturalWord later := by
  simp only [naturalWord, List.flatMap_cons, List.cons_append, List.nil_append]

theorem naturalWord_payload_length (digits : List Bool) :
    (digits.flatMap (fun bit => [false,bit])).length = 2 * digits.length := by
  induction digits with
  | nil => rfl
  | cons bit later ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil,
      ih]
    omega

theorem naturalWord_length (digits : List Bool) :
    (naturalWord digits).length = 2 * digits.length + 2 := by
  simp only [naturalWord, List.length_append, naturalWord_payload_length,
    List.length_cons, List.length_nil]

theorem naturalCompact_halt (left right : List Bool) :
    TM0.step naturalCompactMachine (state 11 left right) = none := by
  simp [TM0.step,naturalCompactMachine,state]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPairedArchive
