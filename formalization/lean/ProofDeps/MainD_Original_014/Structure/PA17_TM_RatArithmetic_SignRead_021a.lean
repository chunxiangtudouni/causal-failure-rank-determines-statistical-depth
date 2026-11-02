module
public import Structure.PA17_TM_Division_Compose_006a

/-! Observe the retained sx cell two positions left of Nx, without writing
or clearing it. The bit below describes actual tape content, not an input flag
or code argument. ONE seven-label kernel precedes all tapes and signs. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSignRead021

open Turing

def readRightPort (bit : Bool) : Fin 7 := if bit then 4 else 3
def readPort (bit : Bool) : Fin 7 := if bit then 6 else 5

def sensorMachine : Machine 6 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .left)
  | 1 => some (2,.move .left)
  | 2 => some (readRightPort symbol,.move .right)
  | 3 => some (5,.move .right)
  | 4 => some (6,.move .right)
  | _ => none

def sensorState (q : Fin 7) (left right : List Bool) : MachineState 6 :=
  ⟨q,Tape.mk₂ left right⟩

def sensorInitial (archive : List Bool) (bit : Bool) (right : List Bool) : MachineState 6 :=
  sensorState 0 (false::bit::archive) right

def sensorFinal (archive : List Bool) (bit : Bool) (right : List Bool) : MachineState 6 :=
  sensorState (readPort bit) (false::bit::archive) right

def sensorTrace (archive : List Bool) (bit : Bool) (right : List Bool) : List (MachineState 6) :=
  [sensorInitial archive bit right,
   sensorState 1 (bit::archive) (false::right),
   sensorState 2 archive (bit::false::right),
   sensorState (readRightPort bit) (bit::archive) (false::right),
   sensorFinal archive bit right]

/-- The actual symbol read at label2 selects the two physical return paths.
Both LEFTs and RIGHTs occur on this same tape; sx and all other cells survive. -/
theorem sensor_runsFrom (archive : List Bool) (bit : Bool) (right : List Bool) :
    PSTRTMSeq005.RunsFrom sensorMachine (sensorInitial archive bit right)
      (sensorTrace archive bit right) (sensorFinal archive bit right) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · cases bit <;> simp [sensorTrace,sensorInitial,sensorFinal,List.isChain_cons_cons,
      TM0.step,sensorMachine,sensorState,readRightPort,readPort,Tape.mk₂]
  · cases bit <;> simp [TM0.step,sensorMachine,sensorFinal,sensorState,readPort]

theorem sensor_same_tape (archive : List Bool) (bit : Bool) (right : List Bool) :
    (sensorFinal archive bit right).Tape = (sensorInitial archive bit right).Tape := rfl

theorem sensor_final_label (archive : List Bool) (bit : Bool) (right : List Bool) :
    (sensorFinal archive bit right).q.val = if bit then 6 else 5 := by
  cases bit <;> rfl

theorem sensorTrace_length (archive : List Bool) (bit : Bool) (right : List Bool) :
    (sensorTrace archive bit right).length = 5 := rfl

theorem sensor_prefix_space (archive : List Bool) (bit : Bool) (right : List Bool)
    (prefixLength chargedLength : Nat) :
    visitedSpace sensorMachine chargedLength ((sensorTrace archive bit right).take prefixLength) ≤
      chargedLength+11 := by
  have hs := PSTRTMTrace002.visitedSpace_le sensorMachine chargedLength
    ((sensorTrace archive bit right).take prefixLength)
  have hp : ((sensorTrace archive bit right).take prefixLength).length ≤ 5 := by
    have ht := sensorTrace_length archive bit right
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSignRead021
