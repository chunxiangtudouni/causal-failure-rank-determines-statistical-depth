module
public import Common.PSTR_TM_ThresholdCopyAppend_130

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyRestore131
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCopyCode126 PSTRTMThresholdCopyRoundLift129 PSTRTMThresholdCopyAppend130

def initial (bit : Bool) (left : List Bool) : List Bool → List Bool → MachineState 130
  | [],tail => savedState bit 37 left (false::tail)
  | digit::earlier,tail => savedState bit 37 (digit::(PSTRTMRawNat010.leftBlocks earlier++false::left)) (true::tail)

/-- Actual return stops at the temporary FALSE source flag, writes TRUE
there, and physically moves to the next data cell. The original saved
source data bit and every other context cell remain unchanged. -/
def loopTrace (bit : Bool) (left : List Bool) : List Bool → List Bool → List (MachineState 130)
  | [],tail => [savedState bit 37 left (false::tail),savedState bit 39 left (true::tail),state 34 (true::left) tail]
  | digit::earlier,tail => initial bit left (digit::earlier) tail ::
      savedState bit 38 (PSTRTMRawNat010.leftBlocks earlier++false::left) (digit::true::tail) ::
      loopTrace bit left earlier (digit::true::tail)

theorem loop_head (bit : Bool) (left earlier tail : List Bool) :
    (loopTrace bit left earlier tail).head?=some (initial bit left earlier tail) := by cases earlier <;> rfl

theorem loop_last (bit : Bool) (left earlier tail : List Bool) :
    (loopTrace bit left earlier tail).getLast?=some
      (state 34 (true::left) (PSTRTMIncrement009.blocks earlier.reverse++tail)) := by
  induction earlier generalizing tail with
  | nil => rfl
  | cons digit earlier ih =>
    have hne : loopTrace bit left earlier (digit::true::tail)≠[] := by
      intro h
      have hh := loop_head bit left earlier (digit::true::tail)
      simp [h] at hh
    simp only [loopTrace,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMIncrement009.blocks,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem loop_length (bit : Bool) (left earlier tail : List Bool) :
    (loopTrace bit left earlier tail).length=2*earlier.length+3 := by
  induction earlier generalizing tail with
  | nil => rfl
  | cons digit earlier ih => simp only [loopTrace,List.length_cons,ih]; omega

theorem loop_chain (bit : Bool) (left earlier tail : List Bool) :
    (loopTrace bit left earlier tail).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) := by
  induction earlier generalizing tail with
  | nil => cases bit <;> simp [loopTrace,List.isChain_cons_cons,Turing.TM0.step,copyMachine,savedState,phaseLabel,state,Turing.Tape.mk₂]
  | cons digit earlier ih =>
    apply List.isChain_cons_cons.mpr
    constructor
    · cases bit <;> simp [initial,Turing.TM0.step,copyMachine,savedState,phaseLabel,state,Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [loop_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      cases earlier <;> cases bit <;>
        simp [initial,PSTRTMRawNat010.leftBlocks,Turing.TM0.step,copyMachine,savedState,phaseLabel,state,Turing.Tape.mk₂]
    · exact ih _

def restoreTrace (bit : Bool) (left earlier tail : List Bool) : List (MachineState 130) :=
  savedState bit 36 (PSTRTMRawNat010.leftBlocks earlier++false::left) tail :: loopTrace bit left earlier tail

theorem restore_head (bit : Bool) (left earlier tail : List Bool) : (restoreTrace bit left earlier tail).head?=some
    (savedState bit 36 (PSTRTMRawNat010.leftBlocks earlier++false::left) tail) := rfl

theorem restore_last (bit : Bool) (left earlier tail : List Bool) : (restoreTrace bit left earlier tail).getLast?=some
    (state 34 (true::left) (PSTRTMIncrement009.blocks earlier.reverse++tail)) := by
  have hne : loopTrace bit left earlier tail≠[] := by
    intro h
    have hh := loop_head bit left earlier tail
    simp [h] at hh
  rw [restoreTrace,List.getLast?_cons_of_ne_nil hne,loop_last]

theorem restore_length (bit : Bool) (left earlier tail : List Bool) :
    (restoreTrace bit left earlier tail).length=2*earlier.length+4 := by
  simp only [restoreTrace,List.length_cons,loop_length]

theorem restore_chain (bit : Bool) (left earlier tail : List Bool) :
    (restoreTrace bit left earlier tail).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) := by
  apply List.isChain_cons.mpr
  constructor
  · intro after ha
    rw [loop_head] at ha
    have he := Option.mem_some_iff.mp ha
    subst after
    cases earlier <;> cases bit <;>
      simp [initial,PSTRTMRawNat010.leftBlocks,Turing.TM0.step,copyMachine,savedState,phaseLabel,state,Turing.Tape.mk₂]
  · exact loop_chain bit left earlier tail

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyRestore131
