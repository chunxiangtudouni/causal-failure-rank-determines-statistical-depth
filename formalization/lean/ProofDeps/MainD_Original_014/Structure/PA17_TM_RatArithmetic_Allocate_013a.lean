module
public import Common.PSTR_TM_Seq_005

/-! First actual allocation step. Move an OWN right endmarker by one cell,
really clearing its old cell and writing its new one. This does not yet
implement the width-driven quadratic gap allocator. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocate013

open Turing

def extendMarkerMachine : Machine 3 := fun q _symbol =>
  match q.val with
  | 0 => some (1,.write false)
  | 1 => some (2,.move .right)
  | 2 => some (3,.write true)
  | _ => none

def markerState (q : Fin 4) (left right : List Bool) : MachineState 3 :=
  ⟨q,Tape.mk₂ left right⟩

def extendMarkerTrace (left suffix : List Bool) : List (MachineState 3) :=
  [markerState 0 left (true::false::suffix),
    markerState 1 left (false::false::suffix),
    markerState 2 (false::left) (false::suffix),
    markerState 3 (false::left) (true::suffix)]

theorem extendMarker_runsFrom (left suffix : List Bool) :
    PSTRTMSeq005.RunsFrom extendMarkerMachine
      ⟨0,Tape.mk₂ left (true::false::suffix)⟩ (extendMarkerTrace left suffix)
      ⟨3,Tape.mk₂ (false::left) (true::suffix)⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [extendMarkerTrace,markerState,List.isChain_cons_cons,
      TM0.step,extendMarkerMachine,Tape.mk₂]
  · simp [TM0.step,extendMarkerMachine,Tape.mk₂]

theorem extendMarker_length (left suffix : List Bool) :
    (extendMarkerTrace left suffix).length = 4 := rfl

theorem extendMarker_prefix_space (left suffix : List Bool) (prefixLength inputLength : Nat) :
    visitedSpace extendMarkerMachine inputLength ((extendMarkerTrace left suffix).take prefixLength) ≤
      inputLength+9 := by
  have hs := PSTRTMTrace002.visitedSpace_le extendMarkerMachine inputLength
    ((extendMarkerTrace left suffix).take prefixLength)
  have hl : ((extendMarkerTrace left suffix).take prefixLength).length ≤ 4 := by
    simp only [List.length_take,extendMarker_length]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocate013
