module
public import Common.PSTR_TM_Overlap_132

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyBridges133
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCopyCode126 PSTRTMThresholdCopyRoundLift129 PSTRTMThresholdCopyAppend130

/-- A real source digit is read into finite control, and its flag is
actually cleared before moving to the remaining original source field. -/
def startTrace (bit : Bool) (left tail : List Bool) : List (MachineState 130) :=
  [state 34 left (bit::true::tail),state (if bit then 36 else 35) (bit::left) (true::tail),
    savedState bit 0 (bit::left) (false::tail),savedState bit 1 (false::bit::left) tail]

theorem start_head (bit : Bool) (left tail : List Bool) : (startTrace bit left tail).head?=some
    (state 34 left (bit::true::tail)) := rfl

theorem start_last (bit : Bool) (left tail : List Bool) : (startTrace bit left tail).getLast?=some
    (savedState bit 1 (false::bit::left) tail) := rfl

theorem start_chain (bit : Bool) (left tail : List Bool) :
    (startTrace bit left tail).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) := by
  cases bit <;> simp [startTrace,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,savedState,phaseLabel,Turing.Tape.mk₂]

def markerTrace (bit target : Bool) (left tail : List Bool) : List (MachineState 130) :=
  [savedState bit (if target then 9 else 3) left (true::false::tail),
    savedState bit (if target then 10 else 4) (true::left) (false::tail),
    savedState bit (if target then 11 else 5) (false::true::left) tail]

theorem marker_head (bit target : Bool) (left tail : List Bool) : (markerTrace bit target left tail).head?=some
    (savedState bit (if target then 9 else 3) left (true::false::tail)) := rfl

theorem marker_last (bit target : Bool) (left tail : List Bool) : (markerTrace bit target left tail).getLast?=some
    (savedState bit (if target then 11 else 5) (false::true::left) tail) := rfl

theorem marker_chain (bit target : Bool) (left tail : List Bool) :
    (markerTrace bit target left tail).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) := by
  cases bit <;> cases target <;>
    simp [markerTrace,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,savedState,phaseLabel,Turing.Tape.mk₂]

/-- The actual four-cell0010 boundary is crossed LEFT, preserving the
whole tape. `source` selects the two fixed control sites20 or32. -/
def fourLeftTrace (bit source : Bool) (archive tail : List Bool) : List (MachineState 130) :=
  [savedState bit (if source then 32 else 20) (false::true::false::false::archive) tail,
    savedState bit (if source then 33 else 21) (true::false::false::archive) (false::tail),
    savedState bit (if source then 34 else 22) (false::false::archive) (true::false::tail),
    savedState bit (if source then 35 else 23) (false::archive) (false::true::false::tail),
    savedState bit (if source then 36 else 24) archive (false::false::true::false::tail)]

theorem fourLeft_head (bit source : Bool) (archive tail : List Bool) : (fourLeftTrace bit source archive tail).head?=some
    (savedState bit (if source then 32 else 20) (false::true::false::false::archive) tail) := rfl

theorem fourLeft_last (bit source : Bool) (archive tail : List Bool) : (fourLeftTrace bit source archive tail).getLast?=some
    (savedState bit (if source then 36 else 24) archive (false::false::true::false::tail)) := rfl

theorem fourLeft_chain (bit source : Bool) (archive tail : List Bool) :
    (fourLeftTrace bit source archive tail).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) := by
  cases bit <;> cases source <;>
    simp [fourLeftTrace,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,savedState,phaseLabel,Turing.Tape.mk₂]

def twoLeftTrace (bit : Bool) (archive tail : List Bool) : List (MachineState 130) :=
  [savedState bit 27 (false::false::archive) tail,savedState bit 28 (false::archive) (false::tail),
    savedState bit 29 archive (false::false::tail)]

theorem twoLeft_head (bit : Bool) (archive tail : List Bool) : (twoLeftTrace bit archive tail).head?=some
    (savedState bit 27 (false::false::archive) tail) := rfl

theorem twoLeft_last (bit : Bool) (archive tail : List Bool) : (twoLeftTrace bit archive tail).getLast?=some
    (savedState bit 29 archive (false::false::tail)) := rfl

theorem twoLeft_chain (bit : Bool) (archive tail : List Bool) :
    (twoLeftTrace bit archive tail).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) := by
  cases bit <;> simp [twoLeftTrace,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,savedState,phaseLabel,Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyBridges133
