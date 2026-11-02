module
public import Common.PSTR_TM_ThresholdDepthLoopZero_176

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopNext177
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCounterReturn175

/-- The first real gap FALSE is the162 call guard; every other actual
gap cell, decremented depth flag, and risk archive cell is its archive. -/
def callArchive (archive depth : List Bool) (gap : Nat) : List Bool :=
  false::(PSTRTMThresholdCounterSeek169.gaps gap++returnLeft archive depth)

def nextValue (value : Nat) : Nat := Nat.clog 2 (value+2)

/-- This is a ghost physical-layout measure, not a code or input field.
It records exactly the extra cleared pairs really produced by123. -/
def nextGap (value gap : Nat) : Nat := gap+2*PSTRTMB1RunFrame122.width 1 (value+2)+2

theorem call_input_tape (archive depth : List Bool) (value gap : Nat) :
    (returnFinal archive depth value gap).Tape=Turing.Tape.mk₂ (false::callArchive archive depth gap)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value)) := by
  rw [return_final_tape]
  simp only [PSTRTMThresholdDepthEntry171.initialLeft,PSTRTMThresholdCounterSeek169.gaps,
    List.cons_append,callArchive,returnLeft]

def callTrace (archive depth : List Bool) (value gap : Nat) : List (MachineState 357) :=
  PSTRTMThresholdNextFrame162.nextTrace (callArchive archive depth gap) value

def callFinal (archive depth : List Bool) (value gap : Nat) : MachineState 357 :=
  PSTRTMThresholdNextFrame162.nextFinal (callArchive archive depth gap) value

theorem call_runsFrom (archive depth : List Bool) (value gap : Nat) :
    PSTRTMSeq005.RunsFrom PSTRTMThresholdNextFrame162.nextMachine
      ⟨0,(returnFinal archive depth value gap).Tape⟩ (callTrace archive depth value gap) (callFinal archive depth value gap) := by
  rw [call_input_tape]
  exact PSTRTMThresholdNextFrame162.next_runsFrom _ _

theorem cleared_left (archive depth : List Bool) (value gap : Nat) :
    List.replicate (4*PSTRTMB1RunFrame122.width 1 (value+2)+5) false++callArchive archive depth gap=
      PSTRTMThresholdDepthEntry171.initialLeft archive (PSTRTMThresholdCountdownCode164.predDigits depth)
        (nextGap value gap+1) := by
  let width := PSTRTMB1RunFrame122.width 1 (value+2)
  let tail := returnLeft archive depth
  change List.replicate (4*width+5) false++false::(PSTRTMThresholdCounterSeek169.gaps gap++tail)=
    PSTRTMThresholdCounterSeek169.gaps (gap+2*width+2+1)++tail
  rw [PSTRTMThresholdCounterSeek169.gaps_replicate,PSTRTMThresholdCounterSeek169.gaps_replicate]
  have he : 4*width+5+1+2*gap=2*(gap+2*width+2+1) := by omega
  calc
    List.replicate (4*width+5) false++false::(List.replicate (2*gap) false++tail)=
        (List.replicate (4*width+5) false++[false])++(List.replicate (2*gap) false++tail) := by
          simp only [List.append_assoc,List.singleton_append]
    _=List.replicate (4*width+5+1) false++(List.replicate (2*gap) false++tail) := by
      rw [←List.replicate_succ']
    _=(List.replicate (4*width+5+1) false++List.replicate (2*gap) false)++tail := by
      rw [List.append_assoc]
    _=List.replicate (4*width+5+1+2*gap) false++tail := by rw [←List.replicate_add]
    _=List.replicate (2*(gap+2*width+2+1)) false++tail := by rw [he]

/-- ENTIRE actual next-call endpoint. The gap grows by an EVEN number
of real cleared cells, so the next depth seek/zero-test/right pair seek
remain aligned. No List-tail zero is substituted for two physical cells. -/
theorem call_final_tape (archive depth : List Bool) (value gap : Nat) :
    (callFinal archive depth value gap).Tape=Turing.Tape.mk₂
      (PSTRTMThresholdDepthEntry171.initialLeft archive (PSTRTMThresholdCountdownCode164.predDigits depth)
        (nextGap value gap+1))
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (nextValue value))) := by
  have h := PSTRTMThresholdNextFrame162.next_final_tape (callArchive archive depth gap) value
  rw [cleared_left archive depth value gap] at h
  exact h

theorem call_length_le (archive depth : List Bool) (value gap : Nat) :
    (callTrace archive depth value gap).length≤8192*(natBits value+1)^2 :=
  PSTRTMThresholdNextFrame162.next_length_le _ _

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopNext177
