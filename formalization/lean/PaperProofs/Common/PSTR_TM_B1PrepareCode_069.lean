module
public import PaperProofs.Common.PSTR_TM_ColumnRewind_067
public import PaperProofs.Common.PSTR_TM_CompareRun_059

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1PrepareCode069
open PaperProofs.Common.Native.RationalControllerComputation

def embedRewind (q : Fin 6) : Fin 32 := ⟨26 + q.val, by have h := q.isLt; omega⟩
def liftRewind (old : MachineState 5) : MachineState 31 := ⟨embedRewind old.q, old.Tape⟩

/-- Actual once-only B1 initialization: scan real input flags, allocate
one HIGH zero column, OWN00, marker10 and binary counter01 on REAL blanks,
then execute the existing real rewind. No field is supplied in the input. -/
def prepareMachine : Machine 31 := fun q symbol =>
  if h : q.val < 26 then
    match q.val with
    | 0 => some (1, .move .right)
    | 1 => some (if symbol then 0 else 2, if symbol then .move .right else .move .left)
    | 2 => some (3, .write false)
    | 3 => some (4, .move .right)
    | 4 => some (5, .write true)
    | 5 => some (6, .move .right)
    | 6 => some (7, .write false)
    | 7 => some (8, .move .right)
    | 8 => some (9, .write true)
    | 9 => some (10, .move .right)
    | 10 => some (11, .write false)
    | 11 => some (12, .move .right)
    | 12 => some (13, .write false)
    | 13 => some (14, .move .right)
    | 14 => some (15, .write true)
    | 15 => some (16, .move .right)
    | 16 => some (17, .write false)
    | 17 => some (18, .move .right)
    | 18 => some (19, .write false)
    | 19 => some (20, .move .right)
    | 20 => some (21, .write true)
    | 21 => some (22, .move .left)
    | 22 => some (23, .move .left)
    | 23 => some (24, .move .left)
    | 24 => some (25, .move .left)
    | 25 => some (26, .move .left)
    | _ => none
  else (PSTRTMColumnRewind067.rewindMachine ⟨q.val - 26, by omega⟩ symbol).map
    (fun (next, statement) => (embedRewind next, statement))

def state (q : Fin 32) (left right : List Bool) : MachineState 31 := ⟨q, Turing.Tape.mk₂ left right⟩
def paddedPairs (pairs : List (Bool × Bool)) : List (Bool × Bool) := pairs ++ [(false,false)]
def suffix : List Bool := [false,false,true,false,false,true]
def preparedWord (pairs : List (Bool × Bool)) : List Bool := PSTRTMBinaryAdd024.operandColumns (paddedPairs pairs) ++ suffix

theorem rewind_step (before : MachineState 5) :
    Turing.TM0.step prepareMachine (liftRewind before) =
      (Turing.TM0.step PSTRTMColumnRewind067.rewindMachine before).map liftRewind := by
  cases before with
  | mk q tape =>
    simp only [Turing.TM0.step, prepareMachine, liftRewind, embedRewind,
      show ¬26 + q.val < 26 by omega, dite_false, Nat.add_sub_cancel_left, Fin.eta]
    cases hc : PSTRTMColumnRewind067.rewindMachine q tape.head with
    | none => simp
    | some command => obtain ⟨next, statement⟩ := command; cases statement <;> simp [liftRewind, embedRewind]

theorem rewind_chain (trace : List (MachineState 5))
    (hc : trace.IsChain (fun a b => Turing.TM0.step PSTRTMColumnRewind067.rewindMachine a = some b)) :
    (trace.map liftRewind).IsChain (fun a b => Turing.TM0.step prepareMachine a = some b) := by
  apply (List.isChain_map _).mpr
  apply hc.imp
  intro before after hs
  rw [rewind_step, hs]
  rfl

theorem prepare_halt (left right : List Bool) : Turing.TM0.step prepareMachine (state 31 left right) = none := by
  simp [Turing.TM0.step, prepareMachine, state, PSTRTMColumnRewind067.rewindMachine]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1PrepareCode069
