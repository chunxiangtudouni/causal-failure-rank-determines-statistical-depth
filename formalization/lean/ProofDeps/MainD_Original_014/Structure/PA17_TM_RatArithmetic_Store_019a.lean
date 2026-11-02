module
public import Structure.PA17_TM_RatArithmetic_Parse_002c

/-! Real constant-size writes around an arithmetic callee's canonical rawNat.
The caller supplies two actual left reserve cells and a genuinely blank right
tail. No numeric value, bit length, parsed field or answer is supplied to code. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticStore019

open Turing

attribute [local simp] PSTRTMRawNat010.blank_single_false

def anchorMachine : Machine 5 := fun q _symbol =>
  match q.val with
  | 0 => some (1,.move .left)
  | 1 => some (2,.move .left)
  | 2 => some (3,.write true)
  | 3 => some (4,.move .right)
  | 4 => some (5,.move .right)
  | _ => none

def anchorState (q : Fin 6) (left right : List Bool) : MachineState 5 :=
  ⟨q,Tape.mk₂ left right⟩

def anchorTrace (archive raw : List Bool) : List (MachineState 5) :=
  [anchorState 0 (false::false::archive) raw,
   anchorState 1 (false::archive) (false::raw),
   anchorState 2 archive (false::false::raw),
   anchorState 3 archive (true::false::raw),
   anchorState 4 (true::archive) (false::raw),
   anchorState 5 (false::true::archive) raw]

theorem anchor_runsFrom (archive raw : List Bool) :
    PSTRTMSeq005.RunsFrom anchorMachine
      (anchorState 0 (false::false::archive) raw) (anchorTrace archive raw)
      (anchorState 5 (false::true::archive) raw) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [anchorTrace,List.isChain_cons_cons,TM0.step,anchorMachine,anchorState,Tape.mk₂]
  · simp [TM0.step,anchorMachine,anchorState]

theorem anchorTrace_length (archive raw : List Bool) :
    (anchorTrace archive raw).length = 6 := rfl

def closeMachine : Machine 3 := fun q _symbol =>
  match q.val with
  | 0 => some (1,.write false)
  | 1 => some (2,.move .right)
  | 2 => some (3,.write true)
  | _ => none

def closeState (q : Fin 4) (left right : List Bool) : MachineState 3 :=
  ⟨q,Tape.mk₂ left right⟩

def closeTrace (left : List Bool) : List (MachineState 3) :=
  [closeState 0 left [],closeState 1 left [false],
   closeState 2 (false::left) [],closeState 3 (false::left) [true]]

theorem close_runsFrom (left : List Bool) :
    PSTRTMSeq005.RunsFrom closeMachine (closeState 0 left [])
      (closeTrace left) (closeState 3 (false::left) [true]) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [closeTrace,List.isChain_cons_cons,TM0.step,closeMachine,closeState,Tape.mk₂]
  · simp [TM0.step,closeMachine,closeState]

theorem closeTrace_length (left : List Bool) : (closeTrace left).length = 4 := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticStore019
