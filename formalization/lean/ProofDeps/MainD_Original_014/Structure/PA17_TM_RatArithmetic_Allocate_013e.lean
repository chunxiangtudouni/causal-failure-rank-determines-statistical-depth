module
public import Structure.PA17_TM_RatArithmetic_Allocate_013d
public import Structure.PA17_TM_Division_Compose_006a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocate013

open Turing PA17TMDivisionCompose006

def setMarkerMachine (bit : Bool) : Machine 1 := fun q _symbol =>
  if q.val=0 then some (1,.write bit) else none

def setMarkerTrace (old bit : Bool) (left suffix : List Bool) : List (MachineState 1) :=
  [seekState 0 left (old::suffix),seekState 1 left (bit::suffix)]

theorem setMarker_runsFrom (old bit : Bool) (left suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (setMarkerMachine bit) (seekState 0 left (old::suffix))
      (setMarkerTrace old bit left suffix) (seekState 1 left (bit::suffix)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [setMarkerTrace,List.isChain_cons_cons,TM0.step,setMarkerMachine,seekState,Tape.mk₂]
  · simp [TM0.step,setMarkerMachine,seekState]

def expandCap (k : Nat) : Nat := totalStates 4 (3*k+1)

def expandFamily (k : Nat) (phase : Fin 5) : Machine (3*k+1) :=
  match phase.val with
  | 0 => padMachine (by omega : 1≤3*k+1) (setMarkerMachine true)
  | 1 => padMachine (by omega : 1≤3*k+1) (gapSeekMachine .right)
  | 2 => padMachine (by omega : 3*k≤3*k+1) (gapMachine k)
  | 3 => padMachine (by omega : 1≤3*k+1) (gapSeekMachine .left)
  | _ => padMachine (by omega : 1≤3*k+1) (setMarkerMachine false)

def expandPorts {k : Nat} (phase : Fin 5) (_localLabel : Fin (3*k+2)) : Option (Fin 5 × Fin (3*k+2)) :=
  if h : phase.val<4 then some (⟨phase.val+1,by omega⟩,0) else none

/-- Fixed five-stage finite control: restore the old footer TRUE, actually
seek the far marker, grow k cells, actually return, reclamp the footer FALSE.
The current gap length is read by scans, never supplied to this code. -/
def expandMachine (k : Nat) : Machine (expandCap k) :=
  blockMachine (expandFamily k) expandPorts

def expandLift {a : Nat} (k : Nat) (phase : Fin 5) (h : a≤3*k+1)
    (state : MachineState a) : MachineState (expandCap k) :=
  blockCfg phase (padCfg h state)

def expandLiftTrace {a : Nat} (k : Nat) (phase : Fin 5) (h : a≤3*k+1)
    (trace : List (MachineState a)) : List (MachineState (expandCap k)) :=
  (trace.map (padCfg h)).map (blockCfg phase)

theorem expand_lift_segment {a : Nat} (k : Nat) (phase : Fin 5) (h : a≤3*k+1)
    (machine : Machine a)
    (family : expandFamily k phase=padMachine h machine)
    (first last : MachineState a) (trace : List (MachineState a))
    (run : PSTRTMSeq005.RunsFrom machine first trace last) :
    Segment (expandMachine k) (expandLift k phase h first)
      (expandLiftTrace k phase h trace) (expandLift k phase h last) := by
  have hp := pad_runsFrom h machine first last trace run
  have hf : PSTRTMSeq005.RunsFrom (expandFamily k phase) (padCfg h first)
      (trace.map (padCfg h)) (padCfg h last) := by
    rw [family]
    exact hp
  exact block_segment (expandFamily k) expandPorts phase _ _ _ hf

theorem expand_transfer {a : Nat} (k : Nat) (phase : Fin 5) (hnext : phase.val<4)
    (h : a≤3*k+1) (machine : Machine a)
    (family : expandFamily k phase=padMachine h machine)
    (last : MachineState a) (halt : TM0.step machine last=none) :
    TM0.step (expandMachine k) (expandLift k phase h last) =
      some (blockCfg (⟨phase.val+1,by omega⟩ : Fin 5) ⟨0,last.Tape⟩) := by
  have hp : TM0.step (expandFamily k phase) (padCfg h last)=none := by
    rw [family]
    simp only [pad_step,halt,Option.map_none]
  exact block_transfer (expandFamily k) expandPorts phase (padCfg h last)
    (⟨phase.val+1,by omega⟩,0) hp (by simp only [expandPorts,dite_eq_left hnext])

theorem expand_last_halt {a : Nat} (k : Nat) (h : a≤3*k+1) (machine : Machine a)
    (family : expandFamily k 4=padMachine h machine)
    (last : MachineState a) (halt : TM0.step machine last=none) :
    TM0.step (expandMachine k) (expandLift k 4 h last)=none := by
  have hp : TM0.step (expandFamily k 4) (padCfg h last)=none := by
    rw [family]
    simp only [pad_step,halt,Option.map_none]
  exact block_halt (expandFamily k) expandPorts 4 (padCfg h last) hp (by simp [expandPorts])

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocate013
