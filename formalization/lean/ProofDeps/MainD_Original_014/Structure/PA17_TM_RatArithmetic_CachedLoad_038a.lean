module
public import Structure.PA17_TM_RatArithmetic_FarLoad_031k

/-! Actual cached DATA observation. The same fixed code handles either
first bit. Saved control ports retain the observation through SOURCE and
DEST restoration; no caller-supplied LSB constructs a machine. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing PA17TMDivisionCompose006

def savedPort (bit : Bool) : Fin 5 := if bit then 2 else 1
def restoredPort (bit : Bool) : Fin 5 := if bit then 4 else 3

def readMachine : Machine 4 := padMachine (by decide : 2≤4)
  PA17TMRatArithmeticBookmark014.readClearMachine

/-- The observed bit is selected by the actual incoming control port. -/
def restoreMachine : Machine 4 := fun q _ =>
  match q.val with
  | 1 => some (3,.write false)
  | 2 => some (4,.write true)
  | _ => none

/-- A second real write can reuse the retained observation, for example
at DEST after the source was physically restored and navigation completed. -/
def restoreAgainMachine : Machine 4 := fun q _ =>
  match q.val with
  | 3 => some (1,.write false)
  | 4 => some (2,.write true)
  | _ => none

def roundMachine : Machine 4 := fun q symbol =>
  if q.val=0 then readMachine q symbol else restoreMachine q symbol

def state (q : Fin 5) (left right : List Bool) : MachineState 4 := ⟨q,Tape.mk₂ left right⟩

def readTrace (left : List Bool) (bit : Bool) (suffix : List Bool) : List (MachineState 4) :=
  (PA17TMRatArithmeticBookmark014.readClearTrace left bit suffix).map (padCfg (by decide : 2≤4))

theorem read_runsFrom (left : List Bool) (bit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom readMachine (state 0 left (bit::suffix)) (readTrace left bit suffix)
      (state (savedPort bit) left (false::suffix)) := by
  have h := pad_runsFrom (by decide : 2≤4) PA17TMRatArithmeticBookmark014.readClearMachine _ _ _
    (PA17TMRatArithmeticBookmark014.readClear_runsFrom left bit suffix)
  cases bit <;> exact h

def restoreTrace (left : List Bool) (old bit : Bool) (suffix : List Bool) : List (MachineState 4) :=
  [state (savedPort bit) left (old::suffix),state (restoredPort bit) left (bit::suffix)]

theorem restore_runsFrom (left : List Bool) (old bit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom restoreMachine (state (savedPort bit) left (old::suffix))
      (restoreTrace left old bit suffix) (state (restoredPort bit) left (bit::suffix)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · cases bit <;> simp [restoreTrace,List.isChain_cons_cons,TM0.step,restoreMachine,
      state,savedPort,restoredPort,Tape.mk₂]
  · cases bit <;> simp [TM0.step,restoreMachine,state,restoredPort]

def restoreAgainTrace (left : List Bool) (old bit : Bool) (suffix : List Bool) : List (MachineState 4) :=
  [state (restoredPort bit) left (old::suffix),state (savedPort bit) left (bit::suffix)]

theorem restoreAgain_runsFrom (left : List Bool) (old bit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom restoreAgainMachine (state (restoredPort bit) left (old::suffix))
      (restoreAgainTrace left old bit suffix) (state (savedPort bit) left (bit::suffix)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · cases bit <;> simp [restoreAgainTrace,List.isChain_cons_cons,TM0.step,restoreAgainMachine,
      state,savedPort,restoredPort,Tape.mk₂]
  · cases bit <;> simp [TM0.step,restoreAgainMachine,state,savedPort]

def roundTrace (left : List Bool) (bit : Bool) (suffix : List Bool) : List (MachineState 4) :=
  [state 0 left (bit::suffix),state (savedPort bit) left (false::suffix),
    state (restoredPort bit) left (bit::suffix)]

/-- Both writes are charged, including the all-FALSE case. The head and
ENTIRE tape are restored, and the observed bit remains in the final port. -/
theorem round_runsFrom (left : List Bool) (bit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom roundMachine (state 0 left (bit::suffix)) (roundTrace left bit suffix)
      (state (restoredPort bit) left (bit::suffix)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · cases bit <;> simp [roundTrace,List.isChain_cons_cons,TM0.step,roundMachine,readMachine,
      padMachine,padLabel,PA17TMRatArithmeticBookmark014.readClearMachine,
      PA17TMRatArithmeticBookmark014.readPort,restoreMachine,state,savedPort,restoredPort,Tape.mk₂]
  · cases bit <;> simp [TM0.step,roundMachine,restoreMachine,state,restoredPort]

theorem readTrace_length (left : List Bool) (bit : Bool) (suffix : List Bool) :
    (readTrace left bit suffix).length=2 := rfl
theorem restoreTrace_length (left : List Bool) (old bit : Bool) (suffix : List Bool) :
    (restoreTrace left old bit suffix).length=2 := rfl
theorem restoreAgainTrace_length (left : List Bool) (old bit : Bool) (suffix : List Bool) :
    (restoreAgainTrace left old bit suffix).length=2 := rfl
theorem roundTrace_length (left : List Bool) (bit : Bool) (suffix : List Bool) :
    (roundTrace left bit suffix).length=3 := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
